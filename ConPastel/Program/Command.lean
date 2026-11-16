import ConPastel.Program.Assemble
import ConPastel.Program.Scale
import ConPastel.Translator.Meta.Unit

/-!
# `cake_program`: assemble the translated units into a program

`cake_program P entry` builds, from every registered unit:
* `P.funs`, the single recursive group (one entry per unit);
* `P.cert_k`, unit `%k`'s certificate instantiated at `initEnv` and `P.funs`,
  in registration order (a unit's dependencies are registered before it);
* `P.prog`, the program, and `P.correct`: for every input, `P.prog`
  completes, writing `entry`'s verdict on the input bytes.

The program declares every registered datatype in one `Dtype` (stamps from 2,
in registration order), then the group, then the main program.
-/

namespace ConPastel.Program
open Lean Meta Elab Command ConPastel.Translator.Meta
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- A unit's dependencies, by unit name (older units recorded only keys). -/
def depNamesOf (env : Environment) (u : UnitInfo) : Array Name :=
  if u.depNames.size == u.deps.size then u.depNames
  else u.deps.filterMap fun d => (getUnit? env d).map (·.name)

/-- All units, every unit after its dependencies (independent modules may
have translated the same key: both copies are kept). -/
def unitsInOrder (env : Environment) : Array UnitInfo := Id.run do
  let us := allUnits env
  let mut done : Std.HashSet Name := {}
  let mut out : Array UnitInfo := #[]
  let mut todo := us
  while !todo.isEmpty do
    let (ready, rest) := todo.partition fun u => (depNamesOf env u).all done.contains
    if ready.isEmpty then break
    for u in ready do
      done := done.insert u.name
      out := out.push u
    todo := rest
  return out

def addThm (n : Name) (pf : Expr) : MetaM Unit := do
  let pf ← instantiateMVars pf
  addDecl (Declaration.thmDecl (mkTheoremValEx n [] (← inferType pf) pf []))

def addDef (n : Name) (ty val : Expr) : MetaM Unit :=
  addDecl (Declaration.defnDecl (mkDefinitionValEx n [] ty val .abbrev .safe []))

/-! ## Proof-construction helpers (no kernel string comparisons; see `Scale`) -/

/-- Character codes of a name, as `charKey` computes them. -/
def strKey (s : String) : List Nat := s.toList.map (·.toNat % 256)

def keyLt (a b : String) : Bool := lexLtN (strKey a) (strKey b)

def lit0 (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc) (mkApp (mkConst ``List.nil [0]) ty)

/-- `[Char.ofNat c₁, …]`, the kernel's unfolding of the literal `s`. -/
def charsE (s : String) : Expr :=
  lit0 (mkConst ``Char) (s.toList.map fun c => mkApp (mkConst ``Char.ofNat) (mkRawNatLit c.toNat))

/-- The suffixes of a literal list: `sfx[i]` is the list from element `i` on. -/
def suffixes (ty : Expr) (xs : Array Expr) : Array Expr := Id.run do
  let mut out := #[mkApp (mkConst ``List.nil [0]) ty]
  for x in xs.reverse do
    out := out.push (mkApp3 (mkConst ``List.cons [0]) ty x out.back!)
  return out.reverse

/-- `xs[i] ∈ sfx[0]`, by `mem_tail`s and a `mem_head`. -/
def memChain (ty : Expr) (xs sfx : Array Expr) (i : Nat) : Expr := Id.run do
  let a := xs[i]!
  let mut p := mkApp3 (mkConst ``mem_head) ty a sfx[i+1]!
  for j' in [0:i] do
    let j := i - 1 - j'
    p := mkApp5 (mkConst ``mem_tail) ty a xs[j]! sfx[j+1]! p
  return p

def addThmT (n : Name) (ty pf : Expr) : MetaM Unit :=
  addDecl (Declaration.thmDecl (mkTheoremValEx n [] ty pf []))

def memTy (ty a l : Expr) : MetaM Expr := mkAppOptM ``Membership.mem #[ty, none, none, l, a]

/-- `distinctN`/`sortedN` of the keys of `names` (a constant), checked by the kernel. -/
def keysCheck (n : Name) (check : Name) (namesC : Expr) : MetaM Expr := do
  let lc := mkApp (mkConst ``List [0]) (mkConst ``Char)
  let keys := mkApp4 (mkConst ``List.map [0, 0]) lc (mkApp (mkConst ``List [0]) (mkConst ``Nat)) (mkConst ``charKey) namesC
  let ty ← mkEq (mkApp (mkConst check) keys) (mkConst ``Bool.true)
  addThmT n ty (← mkEqRefl (mkConst ``Bool.true))
  return mkConst n

/-- `xs.Nodup` for `xs` a list of names, given (in order) as `names`. -/
def nodupOfNames (lem : Name) (xs namesC keysPf : Expr) : MetaM Expr := do
  return mkApp4 (mkConst lem) xs namesC (← mkEqRefl xs) keysPf

/-- The CakeML string of a name expression (`ofString "…"`, possibly behind constants). -/
partial def nameStr (e : Expr) : MetaM String := do
  let e := e.consumeMData
  if let some s := ConPastel.Translator.Meta.mlStringLit? e then return s
  if e.isAppOfArity ``Flapjack.Basis.Pure.MlString.ofString 1 then
    if let .lit (.strVal s) := (← whnf e.appArg!).consumeMData then return s
  if let .const c ls := e.getAppFn then
    if c != ``Flapjack.Basis.Pure.MlString.ofString then
      if ((← getEnv).find? c |>.bind (·.value?)).isSome then
        let ci ← getConstInfo c
        return ← nameStr ((ci.instantiateValueLevelParams! ls).beta e.getAppArgs)
  throwError "cake_program: not a name literal {e}"

/-- Prove a constructor-environment fact (`HasBoolCons`, `T.cakeHasCons`, …): a
structure or conjunction of `nsLookup envCc (.short c) = some v`, each from
membership in the flat environment `envCc = .bind cl []`. -/
partial def proveCons (lookupPf : String → Expr → Expr → MetaM Expr) (goal : Expr) : MetaM Expr := do
  let goal := goal.consumeMData
  match goal.getAppFnArgs with
  | (``And, #[a, b]) => return mkApp4 (mkConst ``And.intro) a b (← proveCons lookupPf a) (← proveCons lookupPf b)
  | (``Eq, #[_, lhs, rhs]) =>
    let (``Flapjack.NamespaceHOL.nsLookup, #[_, _, _, _, _, _, id]) := lhs.getAppFnArgs
      | throwError "cake_program: unexpected constructor fact {goal}"
    let (``Flapjack.NamespaceHOL.Ident.short, #[_, _, c]) := id.getAppFnArgs
      | throwError "cake_program: unexpected constructor fact {goal}"
    let (``Option.some, #[_, v]) := rhs.getAppFnArgs
      | throwError "cake_program: unexpected constructor fact {goal}"
    lookupPf (← nameStr c) c v
  | (n, args) =>
    if isStructure (← getEnv) n then
      let ctor := getStructureCtor (← getEnv) n
      let ty ← instantiateForall (← inferType (mkConst ctor.name (goal.getAppFn.constLevels!))) args
      let mut pfs := #[]
      let mut t := ty
      while t.isForall do
        let .forallE _ d b _ := t | unreachable!
        let pf ← proveCons lookupPf d
        pfs := pfs.push pf
        t := b.instantiate1 pf
      return mkAppN (mkConst ctor.name goal.getAppFn.constLevels!) (args ++ pfs)
    let some g' ← unfoldDefinition? goal | throwError "cake_program: cannot unfold constructor fact {goal}"
    proveCons lookupPf g'.headBeta

/-- Build the constructor-arity derivation `COk tbl e` for an expression `e`. -/
structure CokCtx where
  tbl : Expr
  /-- per constructor name: its arity and the theorem `(c, n) ∈ tbl` -/
  mems : Std.HashMap String (Nat × Expr)

/-- One head-normalization step towards a constructor application. -/
def unfoldHead? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  let e' ← whnf e
  if e' == e then return none
  return some e'

def whnfPair (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if e.isAppOfArity ``Prod.mk 4 then return e
  return (← whnf e).consumeMData

mutual
partial def cokE (cx : CokCtx) (e : Expr) : StateRefT (Std.HashMap Expr Expr) MetaM Expr := do
  if let some p := (← get).get? e then return p
  let tbl := cx.tbl
  let c (n : Name) := mkApp (mkConst n) tbl
  let p ← match e.consumeMData.getAppFnArgs with
    | (``Exp.raise, #[a]) => pure (mkApp2 (c ``COk.raise) a (← cokE cx a))
    | (``Exp.handle, #[a, cs]) => pure (mkApp4 (c ``COk.handle) a cs (← cokE cx a) (← cokC cx cs))
    | (``Exp.lit, #[l]) => pure (mkApp (c ``COk.lit) l)
    | (``Exp.con, #[o, es]) =>
      match o.consumeMData.getAppFnArgs with
      | (``Option.none, _) => pure (mkApp2 (c ``COk.conNone) es (← cokL cx es))
      | (``Option.some, #[_, id]) =>
        let (``Flapjack.NamespaceHOL.Ident.short, #[_, _, cn]) := id.consumeMData.getAppFnArgs
          | throwError "cake_program: long constructor {id}"
        let s ← nameStr cn
        let some (n, mem) := cx.mems.get? s | throwError "cake_program: undeclared constructor {s}"
        let some esL := (← listElems? es) | throwError "cake_program: constructor arguments {es}"
        unless esL.size == n do throwError "cake_program: constructor {s} has arity {n}, applied to {esL.size}"
        pure (mkApp4 (c ``COk.conShort) cn es mem (← cokL cx es))
      | _ => throwError "cake_program: unexpected constructor {o}"
    | (``Exp.var, #[x]) => pure (mkApp (c ``COk.var) x)
    | (``Exp.fn, #[x, a]) => pure (mkApp3 (c ``COk.fn) x a (← cokE cx a))
    | (``Exp.app, #[op, es]) => pure (mkApp3 (c ``COk.app) op es (← cokL cx es))
    | (``Exp.log, #[op, a, b]) => pure (mkApp5 (c ``COk.log) op a b (← cokE cx a) (← cokE cx b))
    | (``Exp.if_, #[a, b, d]) => pure (mkAppN (c ``COk.if_) #[a, b, d, ← cokE cx a, ← cokE cx b, ← cokE cx d])
    | (``Exp.mat, #[a, cs]) => pure (mkApp4 (c ``COk.mat) a cs (← cokE cx a) (← cokC cx cs))
    | (``Exp.let_, #[x, a, b]) => pure (mkApp5 (c ``COk.let_) x a b (← cokE cx a) (← cokE cx b))
    | (``Exp.letrec, #[fs, b]) => pure (mkApp4 (c ``COk.letrec) fs b (← cokF cx fs) (← cokE cx b))
    | (``Exp.tannot, #[a, t]) => pure (mkApp3 (c ``COk.tannot) a t (← cokE cx a))
    | (``Exp.lannot, #[a, l]) => pure (mkApp3 (c ``COk.lannot) a l (← cokE cx a))
    | _ =>
      let some e' ← unfoldHead? e | throwError "cake_program: unexpected expression {e}"
      cokE cx e'
  modify (·.insert e p)
  return p
partial def listElems? (e : Expr) : MetaM (Option (Array Expr)) := do
  match e.consumeMData.getAppFnArgs with
  | (``List.nil, _) => return some #[]
  | (``List.cons, #[_, h, t]) => return (← listElems? t).map (#[h] ++ ·)
  | _ =>
    let some e' ← unfoldHead? e | return none
    listElems? e'
partial def cokL (cx : CokCtx) (es : Expr) : StateRefT (Std.HashMap Expr Expr) MetaM Expr := do
  match es.consumeMData.getAppFnArgs with
  | (``List.nil, _) => return mkApp (mkConst ``COkL.nil) cx.tbl
  | (``List.cons, #[_, h, t]) => return mkApp5 (mkConst ``COkL.cons) cx.tbl h t (← cokE cx h) (← cokL cx t)
  | _ =>
    let some e' ← unfoldHead? es | throwError "cake_program: unexpected list {es}"
    cokL cx e'
partial def cokC (cx : CokCtx) (cs : Expr) : StateRefT (Std.HashMap Expr Expr) MetaM Expr := do
  match cs.consumeMData.getAppFnArgs with
  | (``List.nil, _) => return mkApp (mkConst ``COkC.nil) cx.tbl
  | (``List.cons, #[_, h, t]) =>
    let (``Prod.mk, #[_, _, p, e]) := (← whnfPair h).getAppFnArgs
      | throwError "cake_program: unexpected clause {h}"
    return mkAppN (mkConst ``COkC.cons) #[cx.tbl, p, e, t, ← cokE cx e, ← cokC cx t]
  | _ =>
    let some e' ← unfoldHead? cs | throwError "cake_program: unexpected clauses {cs}"
    cokC cx e'
partial def cokF (cx : CokCtx) (fs : Expr) : StateRefT (Std.HashMap Expr Expr) MetaM Expr := do
  match fs.consumeMData.getAppFnArgs with
  | (``List.nil, _) => return mkApp (mkConst ``COkF.nil) cx.tbl
  | (``List.cons, #[_, h, t]) =>
    let (``Prod.mk, #[_, _, f, r]) := (← whnfPair h).getAppFnArgs
      | throwError "cake_program: unexpected function {h}"
    let (``Prod.mk, #[_, _, x, e]) := (← whnfPair r).getAppFnArgs
      | throwError "cake_program: unexpected function {h}"
    return mkAppN (mkConst ``COkF.cons) #[cx.tbl, f, x, e, t, ← cokE cx e, ← cokF cx t]
  | _ =>
    let some e' ← unfoldHead? fs | throwError "cake_program: unexpected functions {fs}"
    cokF cx e'
end

/-- A balanced tree of named list chunks: `node` constants are `l ++ r`. -/
inductive FTree
  | leaf (c : Expr) (elems sfx : Array Expr) (start : Nat)
  | node (c : Expr) (l r : FTree) (mid : Nat)
  deriving Inhabited

def FTree.const : FTree → Expr
  | .leaf c .. => c
  | .node c .. => c

/-- `xs[k] ∈ t.const`. -/
partial def FTree.mem (ty : Expr) (t : FTree) (k : Nat) : Expr :=
  match t with
  | .leaf _ elems sfx start => memChain ty elems sfx (k - start)
  | .node _ l r mid =>
    if k < mid then mkApp5 (mkConst ``mem_appL) ty (elems0 l k) l.const r.const (l.mem ty k)
    else mkApp5 (mkConst ``mem_appR) ty (elems0 r k) l.const r.const (r.mem ty k)
where
  elems0 : FTree → Nat → Expr
    | .leaf _ elems _ start, k => elems[k - start]!
    | .node _ l r mid, k => if k < mid then elems0 l k else elems0 r k

/-- The tree over leaves `lo … hi-1`; inner nodes are named `P.funsN_k`. -/
partial def buildTree (P : Name) (fty : Expr) (leaves : Array FTree) (chunk lo hi : Nat) :
    StateRefT Nat MetaM FTree := do
  if hi - lo ≤ 1 then return leaves[lo]!
  let m := (lo + hi) / 2
  let l ← buildTree P fty leaves chunk lo m
  let r ← buildTree P fty leaves chunk m hi
  let k ← modifyGet fun k => (k, k + 1)
  let n := P ++ Name.mkSimple s!"funsN_{k}"
  addDef n (← mkAppM ``List #[fty]) (← mkAppM ``HAppend.hAppend #[l.const, r.const])
  return .node (mkConst n) l r (m * chunk)

def cakeProgram (P entry : Name) : MetaM Unit := do
  let env ← getEnv
  let us := unitsInOrder env
  let some eu := us.find? (·.key == mkConst entry) | throwError "{entry} is not a unit"
  let some ru := us.find? (·.key == mkConst ``ConPastel.Main.revApp) | throwError "revApp is not a unit"
  let t0 ← IO.monoMsNow
  let tick (what : String) : MetaM Unit := do
    ConPastel.Translator.Meta.cakeLog s!"[cake_program] {what} at {(← IO.monoMsNow) - t0}ms"
  -- the datatypes, in stamp order
  let dts := allDatatypes env
  let astT := mkConst ``AstT
  let tyVar ← mkAppM ``AstT.atvar #[mlString "'a"]
  let ctorTy ← mkAppM ``Prod #[mkConst ``ConN, ← mkAppM ``List #[astT]]
  let tdTy ← mkAppM ``Prod #[← mkAppM ``List #[mkConst ``TvarN], ← mkAppM ``Prod #[mkConst ``TypeN,
    ← mkAppM ``List #[ctorTy]]]
  let mut tdEntries : Array Expr := #[]
  let mut tdParts : Array (Expr × Expr × Expr × Array String) := #[]
  for d in dts do
    let ctors ← d.ctors.toList.mapM fun (_, cn, flags) => do
      mkAppM ``Prod.mk #[mlString cn, ← mkListLit astT (List.replicate (flags.toList.filter id).length tyVar)]
    let tv ← mkListLit (mkConst ``TvarN) []
    let tn := mlString d.name.toString
    let cs ← mkListLit ctorTy ctors
    tdParts := tdParts.push (tv, tn, cs, d.ctors.map (·.2.1))
    tdEntries := tdEntries.push (← mkAppM ``Prod.mk #[tv, ← mkAppM ``Prod.mk #[tn, cs]])
  let tdsLit := lit0 tdTy tdEntries.toList
  addDef (P ++ `tds) (mkConst ``TypeDef) tdsLit
  let tds := mkConst (P ++ `tds)
  let envC ← mkAppM ``dtEnv #[tds]
  let envCc ← mkAppM ``SemEnv.c #[envC]
  let lc := mkApp (mkConst ``List [0]) (mkConst ``Char)
  let llc := mkApp (mkConst ``List [0]) lc
  -- `tds.all checkDupCtors`, one type at a time
  let mut hdupPf ← mkEqRefl (mkConst ``Bool.true)
  let tdSfx := suffixes tdTy tdEntries
  for i' in [0:tdParts.size] do
    let i := tdParts.size - 1 - i'
    let (tv, tn, cs, names) := tdParts[i]!
    let nm := P ++ Name.mkSimple s!"dupNames_{i}"
    addDef nm llc (lit0 lc (names.toList.map charsE))
    let keys ← keysCheck (P ++ Name.mkSimple s!"dupKeys_{i}") ``distinctN (mkConst nm)
    let xs ← mkAppM ``List.map #[← mkAppOptM ``Prod.fst #[mkConst ``ConN, ← mkAppM ``List #[astT]], cs]
    let hnd ← nodupOfNames ``nodup_names_distinct xs (mkConst nm) keys
    let hck := mkApp4 (mkConst ``checkDupCtors_of) tv tn cs hnd
    hdupPf := mkAppN (mkConst ``all_cons_of) #[tdTy, mkConst ``checkDupCtors, tdEntries[i]!, tdSfx[i+1]!, hck, hdupPf]
  addThmT (P ++ `hdup) (← mkEq (← mkAppM ``List.all #[tds, mkConst ``checkDupCtors]) (mkConst ``Bool.true)) hdupPf
  let hdup := mkConst (P ++ `hdup)
  tick "hdup"
  -- the flat constructor environment `envCc = .bind cl []`
  let stampT := mkConst ``Stamp
  let clTy ← mkAppM ``Prod #[mkConst ``ConN, ← mkAppM ``Prod #[mkConst ``Nat, stampT]]
  let mut clEntries : Array Expr := #[]
  let mut clNames : Array String := #[]
  let mut tblEntries : Array Expr := #[]
  let mut arity : Array Nat := #[]
  for i' in [0:dts.size] do
    let i := dts.size - 1 - i'
    let d := dts[i]!
    for (_, cn, flags) in d.ctors.reverse do
      let n := (flags.toList.filter id).length
      let ce := mlString cn
      clEntries := clEntries.push (← mkAppM ``Prod.mk #[ce, ← mkAppM ``Prod.mk #[mkRawNatLit n,
        mkApp2 (mkConst ``Stamp.typeStamp) ce (mkRawNatLit (2 + i))]])
      tblEntries := tblEntries.push (← mkAppM ``Prod.mk #[ce, mkRawNatLit n])
      clNames := clNames.push cn
      arity := arity.push n
  let some initV := (← getConstInfo ``ConPastel.initCons).value? | throwError "initCons"
  let some initEs ← listElems? initV | throwError "initCons is not a list literal"
  for e in initEs do
    let (``Prod.mk, #[_, _, ce, r]) := e.getAppFnArgs | throwError "initCons entry {e}"
    let (``Prod.mk, #[_, _, n, _]) := r.getAppFnArgs | throwError "initCons entry {e}"
    let some nv ← (do let v ← whnf n; pure v.rawNatLit?) | throwError "initCons arity {n}"
    clEntries := clEntries.push e
    tblEntries := tblEntries.push (← mkAppM ``Prod.mk #[ce, mkRawNatLit nv])
    clNames := clNames.push (← nameStr ce)
    arity := arity.push nv
  let clSfx := suffixes clTy clEntries
  addDef (P ++ `cl) (← mkAppM ``List #[clTy]) clSfx[0]!
  let cl := mkConst (P ++ `cl)
  let tblTy ← mkAppM ``Prod #[mkConst ``ConN, mkConst ``Nat]
  let tblSfx := suffixes tblTy tblEntries
  addDef (P ++ `tbl) (← mkAppM ``List #[tblTy]) tblSfx[0]!
  let tbl := mkConst (P ++ `tbl)
  let hcTy ← mkEq envCc (← mkAppM ``Namespace.bind #[cl, ← mkListLit (← mkAppM ``Prod
      #[mkConst ``ModN, ← mkAppM ``Namespace #[mkConst ``ModN, mkConst ``ConN,
        ← mkAppM ``Prod #[mkConst ``Nat, stampT]]]) []])
  addThmT (P ++ `hc) hcTy (← mkEqRefl envCc)
  let hc := mkConst (P ++ `hc)
  addDef (P ++ `cnames) llc (lit0 lc (clNames.toList.map charsE))
  let ckeys ← keysCheck (P ++ `ckeys) ``distinctN (mkConst (P ++ `cnames))
  let clKeys ← mkAppM ``List.map #[← mkAppOptM ``Prod.fst #[mkConst ``ConN, ← mkAppM ``Prod #[mkConst ``Nat, stampT]], cl]
  addThmT (P ++ `clNodup) (← mkAppM ``List.Nodup #[clKeys])
    (← nodupOfNames ``nodup_names_distinct clKeys (mkConst (P ++ `cnames)) ckeys)
  let tblKeys ← mkAppM ``List.map #[← mkAppOptM ``Prod.fst #[mkConst ``ConN, mkConst ``Nat], tbl]
  addThmT (P ++ `tblNodup) (← mkAppM ``List.Nodup #[tblKeys])
    (← nodupOfNames ``nodup_names_distinct tblKeys (mkConst (P ++ `cnames)) ckeys)
  tick "constructor environment"
  -- membership theorems for every constructor
  let mut clIdx : Std.HashMap String Nat := {}
  let mut mems : Std.HashMap String (Nat × Expr) := {}
  for i in [0:clNames.size] do
    let s := clNames[i]!
    if clIdx.contains s then continue
    clIdx := clIdx.insert s i
    addThmT (P ++ Name.mkSimple s!"clMem_{i}") (← memTy clTy clEntries[i]! cl) (memChain clTy clEntries clSfx i)
    addThmT (P ++ Name.mkSimple s!"tblMem_{i}") (← memTy tblTy tblEntries[i]! tbl) (memChain tblTy tblEntries tblSfx i)
    mems := mems.insert s (arity[i]!, mkConst (P ++ Name.mkSimple s!"tblMem_{i}"))
  let clIdxF := clIdx
  let lookupPf (s : String) (c v : Expr) : MetaM Expr := do
    let some i := clIdxF.get? s | throwError "cake_program: constructor {s} is not declared"
    return mkAppN (mkConst ``nsLookup_c_of_mem) #[envCc, cl, hc, mkConst (P ++ `clNodup), c, v,
      mkConst (P ++ Name.mkSimple s!"clMem_{i}")]
  let hboolTy ← mkAppM ``ConPastel.Translator.HasBoolCons #[envCc]
  addThmT (P ++ `hbool) hboolTy (← proveCons lookupPf hboolTy)
  let hlistTy ← mkAppM ``ConPastel.Translator.HasListCons #[envCc]
  addThmT (P ++ `hlist) hlistTy (← proveCons lookupPf hlistTy)
  let hbool := mkConst (P ++ `hbool)
  let hlist := mkConst (P ++ `hlist)
  let mut hcsCache : Std.HashMap Name Expr := {}
  for d in dts do
    let ty := mkApp (mkConst (d.name ++ `cakeHasCons)) envCc
    let n := P ++ Name.mkSimple s!"hasCons_{d.stamp}"
    addThmT n ty (← proveCons lookupPf ty)
    hcsCache := hcsCache.insert d.name (mkConst n)
  tick "constructor facts"
  -- the group: entries sorted by name, in a balanced tree of chunks
  let fty ← funTy
  let mut ents0 : Array (String × UnitInfo × Expr) := #[]
  for u in us do
    let (param, body) := match u.kind with
      | .function p b _ => (p, b)
      | .thunk p b => (p, b)
    ents0 := ents0.push (u.cname, u, ← mkAppM ``Prod.mk #[mlString u.cname, ← mkAppM ``Prod.mk #[mlString param, mkConst body]])
  let ents := ents0.qsort fun a b => keyLt a.1 b.1
  for i in [1:ents.size] do
    unless keyLt ents[i-1]!.1 ents[i]!.1 do throwError "cake_program: duplicate unit name {ents[i]!.1}"
  let elems := ents.map (·.2.2)
  let chunk := 32
  let nLeaves := (ents.size + chunk - 1) / chunk
  let mut leaves : Array FTree := #[]
  for li in [0:nLeaves] do
    let es := elems.extract (li * chunk) (min ents.size ((li + 1) * chunk))
    let sfx := suffixes fty es
    let n := P ++ Name.mkSimple s!"funsL_{li}"
    addDef n (← mkAppM ``List #[fty]) sfx[0]!
    leaves := leaves.push (.leaf (mkConst n) es sfx (li * chunk))
  let (tree, _) ← (buildTree P fty leaves chunk 0 nLeaves).run 0
  addDef (P ++ `funs) (← mkAppM ``List #[fty]) tree.const
  let funs := mkConst (P ++ `funs)
  let fstFn ← withLocalDeclD `p fty fun p => do mkLambdaFVars #[p] (← mkAppM ``Prod.fst #[p])
  let namesXs ← mkAppM ``List.map #[fstFn, funs]
  addDef (P ++ `fnames) llc (lit0 lc (ents.toList.map fun e => charsE e.1))
  let fkeys ← keysCheck (P ++ `fkeys) ``sortedN (mkConst (P ++ `fnames))
  addThmT (P ++ `nodup) (← mkAppM ``List.Nodup #[namesXs])
    (← nodupOfNames ``nodup_names_sorted namesXs (mkConst (P ++ `fnames)) fkeys)
  let nodup := mkConst (P ++ `nodup)
  tick "group"
  -- per unit: membership, lookup and entry facts
  let mut lookups : Std.HashMap Name Expr := {}
  let mut finds : Std.HashMap Name Expr := {}
  let mut memsU : Std.HashMap Name Expr := {}
  for k in [0:ents.size] do
    let (cname, u, _) := ents[k]!
    let tag := cname.drop 1
    let (param, body) := match u.kind with
      | .function p b _ => (p, b)
      | .thunk p b => (p, b)
    let g := mlString cname
    let x := mlString param
    let b := mkConst body
    let memN := P ++ Name.mkSimple s!"mem_{tag}"
    addThmT memN (← memTy fty elems[k]! funs) (tree.mem fty k)
    memsU := memsU.insert u.name (mkConst memN)
    let lkN := P ++ Name.mkSimple s!"lookup_{tag}"
    addThmT lkN (← groupLookupTy envC funs cname)
      (mkAppN (mkConst ``groupLookup_of_mem) #[funs, envC, g, x, b, mkConst memN])
    lookups := lookups.insert u.name (mkConst lkN)
    let findTy ← mkEq (← mkAppM ``findRecFun #[g, funs]) (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[x, b]])
    let findN := P ++ Name.mkSimple s!"find_{tag}"
    addThmT findN findTy
      (mkAppN (mkConst ``findRecFun_of_mem) #[mkConst ``VarN, mkConst ``Exp, funs, g, x, b, nodup, mkConst memN])
    finds := finds.insert u.name (mkConst findN)
  tick "lookups"
  -- certificates, in registration order, all under `h : RuntimeAssumptions`
  withLocalDeclD `h (mkConst ``ConPastel.RuntimeAssumptions) fun hrt => do
  let mut certs : Std.HashMap Name Expr := {}
  for u in us do
    let tag := u.cname.drop 1
    let some lkC := lookups.get? u.name | unreachable!
    let some hfind := finds.get? u.name | unreachable!
    let hcs ← u.datatypes.mapM fun T => do
      let some pf := hcsCache.get? T | throwError "cake_program: datatype {T} not assembled"
      pure pf
    let has ← u.assumes.mapM fun a => do
      let i1 := mkIdent `h.numBits
      let i2 := mkIdent `h.mixHash
      let i3 := mkIdent `h.stringHash
      closeWith a (← `(tactic| first | exact $i1:ident | exact $i2:ident | exact $i3:ident))
    let mut args : Array Expr := #[envC, funs, nodup, hfind, hbool, hlist] ++ hcs ++ #[lkC] ++ has
    for p in u.peers do
      let some pf := finds.get? p | throwError "peer {p} of {u.key} not assembled"
      let some pl := lookups.get? p | throwError "peer {p} of {u.key} not assembled"
      args := args ++ #[pf, pl]
    for d in depNamesOf env u do
      let some dl := lookups.get? d | throwError "dependency {d} of {u.key} not assembled"
      let some dc := certs.get? d | throwError "dependency {d} of {u.key} not assembled"
      args := args ++ #[dl, dc]
    ConPastel.Translator.Meta.cakeLog s!"[cake_program] cert {u.name} ({args.size} args)"
    addThm (P ++ Name.mkSimple s!"cert_{tag}") (← mkLambdaFVars #[hrt] (mkAppN (mkConst u.cert) args))
    certs := certs.insert u.name (mkApp (mkConst (P ++ Name.mkSimple s!"cert_{tag}")) hrt)
  tick "certificates"
  -- the constructor-arity condition: one derivation per unit, then up the tree
  let cx : CokCtx := { tbl, mems }
  let mut cokU : Std.HashMap Name Expr := {}
  for (cname, u, _) in ents do
    let body := match u.kind with
      | .function _ b _ => b
      | .thunk _ b => b
    let some v := (← getConstInfo body).value? | throwError "{body} has no value"
    let (pf, _) ← (cokE cx v).run {}
    let n := P ++ Name.mkSimple s!"cok_{cname.drop 1}"
    addThmT n (mkApp2 (mkConst ``COk) tbl (mkConst body)) pf
    cokU := cokU.insert u.name (mkConst n)
  let rec cokTree (t : FTree) : MetaM Expr := do
    match t with
    | .leaf c es sfx start =>
      let mut p := mkApp (mkConst ``COkF.nil) tbl
      for j' in [0:es.size] do
        let j := es.size - 1 - j'
        let (_, u, _) := ents[start + j]!
        let (``Prod.mk, #[_, _, f, r]) := es[j]!.getAppFnArgs | unreachable!
        let (``Prod.mk, #[_, _, x, e]) := r.getAppFnArgs | unreachable!
        let some hu := cokU.get? u.name | unreachable!
        p := mkAppN (mkConst ``COkF.cons) #[tbl, f, x, e, sfx[j+1]!, hu, p]
      let n := c.constName! ++ `cok
      addThmT n (mkApp2 (mkConst ``COkF) tbl c) p
      return mkConst n
    | .node c l r _ =>
      let pl ← cokTree l
      let pr ← cokTree r
      let n := c.constName! ++ `cok
      addThmT n (mkApp2 (mkConst ``COkF) tbl c) (mkAppN (mkConst ``COkF_append) #[tbl, l.const, r.const, pl, pr])
      return mkConst n
  let cokRoot ← cokTree tree
  let conOkPf := mkAppN (mkConst ``conOkFuns_of_COkF) #[tbl, mkConst (P ++ `tblNodup), funs, cokRoot]
  let hcon := mkAppN (mkConst ``group_conOk_of) #[envC, cl, hc, funs, conOkPf]
  tick "constructor arities"
  -- the program and its correctness
  let mainDecs ← mkAppM ``ConPastel.Main.mainDecs #[toExpr eu.cname, toExpr ru.cname]
  let loc := mkConst ``Flapjack.Misc.Location.unknownLoc
  let prog ← mkAppM ``List.cons #[← mkAppM ``Dec.dtype #[loc, tds],
    ← mkAppM ``List.cons #[← mkAppM ``Dec.dletrec #[loc, funs], mainDecs]]
  addDef (P ++ `prog) (← mkAppM ``List #[mkConst ``Dec]) prog
  let some mE := memsU.get? eu.name | unreachable!
  let some mR := memsU.get? ru.name | unreachable!
  let memOf (u : UnitInfo) (m : Expr) : MetaM Expr := do
    let (param, body) := match u.kind with
      | .function p b _ => (p, b)
      | .thunk p b => (p, b)
    return mkAppN (mkConst ``name_mem_of_mem) #[mkConst ``VarN, mkConst ``Exp, funs, mlString u.cname,
      mlString param, mkConst body, m]
  let hmemE ← memOf eu mE
  let hmemR ← memOf ru mR
  let ne (a b : String) : MetaM Expr := do closeWith (mkNot (← mkEq (mlString a) (mlString b))) (← `(tactic| decide))
  let some ce := certs.get? eu.name | unreachable!
  let some cr := certs.get? ru.name | unreachable!
  let pf ← mkAppOptM ``program_completes_dt #[tds, funs, toExpr eu.cname, toExpr ru.cname, mkConst entry, hdup,
    nodup, hcon, hmemE, hmemR, ce, cr, hlist, ← ne eu.cname ConPastel.Main.bufName,
    ← ne eu.cname ConPastel.Main.readAllName, ← ne ru.cname ConPastel.Main.bufName,
    ← ne ru.cname ConPastel.Main.readAllName]
  addThm (P ++ `correct) (← mkLambdaFVars #[hrt] pf)
  tick "correct"

elab "cake_program " P:ident entry:ident : command => do
  let e ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo entry
  liftTermElabM <| cakeProgram P.getId e

end ConPastel.Program
