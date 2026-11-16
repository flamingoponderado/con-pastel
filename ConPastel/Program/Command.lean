import ConPastel.Program.Assemble
import ConPastel.Program.Scale
import ConPastel.Program.Groups
import ConPastel.Translator.Meta.Unit

/-!
# `cake_program`: assemble the translated units into a program

`cake_program P entry` builds, from every registered unit:
* the groups `P.g_k`: classes of mutually recursive units (peers), in
  dependency order, merged into groups of at least 64 units. One `Dletrec`
  per group: CakeML's compiler handles thousands of small groups in minutes,
  but one group of thousands of functions in hours (see `Groups`);
* `P.L_k`, the flat variable bindings before group `k`, and the
  distinctness of all names (`P.nodupL_k`, checked once on character codes);
* `P.cert_k`, unit `%k`'s certificate instantiated at its group's
  environment, with each dependency's lookup proved from membership
  (same group: `groupLookup_of_mem`; earlier group: `depLookup`);
* `P.prog`, the program, and `P.correct`: for every input, `P.prog`
  completes, writing `entry`'s verdict on the input bytes.

The program declares every registered datatype in one `Dtype` (stamps from 2,
in registration order), then the groups, then the main program.
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
      mkAppM ``Prod.mk #[mlString cn, ← mkListLit astT (List.replicate (d.cached.size + (flags.toList.filter id).length) tyVar)]
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
      let n := d.cached.size + (flags.toList.filter id).length
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
  -- the groups: classes of mutually dependent units (peers), in dependency
  -- order, merged into groups of at least `groupSize` units
  let fty ← funTy
  let byName : Std.HashMap Name UnitInfo := us.foldl (fun m u => m.insert u.name u) {}
  let idxOf : Std.HashMap Name Nat := (us.mapIdx fun i u => (u.name, i)).foldl (fun m (n, i) => m.insert n i) {}
  let mut parent : Array Nat := Array.range us.size
  let rec find (parent : Array Nat) (i : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => i
    | f + 1 => if parent[i]! == i then i else find parent parent[i]! f
  for i in [0:us.size] do
    for p in us[i]!.peers do
      let some j := idxOf.get? p | throwError "peer {p} of {us[i]!.key} is not a unit"
      let ri := find parent i us.size
      let rj := find parent j us.size
      if ri != rj then parent := parent.set! ri rj
  let rootOf (i : Nat) : Nat := find parent i us.size
  -- classes in order of first appearance; their dependency classes
  let mut classOrder : Array Nat := #[]
  let mut members : Std.HashMap Nat (Array Nat) := {}
  for i in [0:us.size] do
    let r := rootOf i
    unless members.contains r do classOrder := classOrder.push r
    members := members.insert r ((members.getD r #[]).push i)
  let mut cdeps : Std.HashMap Nat (Array Nat) := {}
  for r in classOrder do
    let mut ds : Array Nat := #[]
    for i in members.getD r #[] do
      for d in depNamesOf env us[i]! do
        let some j := idxOf.get? d | throwError "dependency {d} of {us[i]!.key} is not a unit"
        let rd := rootOf j
        if rd != r && !ds.contains rd then ds := ds.push rd
    cdeps := cdeps.insert r ds
  -- Kahn's algorithm, keeping the original order where possible
  let mut placed : Std.HashSet Nat := {}
  let mut orderC : Array Nat := #[]
  let mut todoC := classOrder
  while !todoC.isEmpty do
    let (ready, rest) := todoC.partition fun r => (cdeps.getD r #[]).all placed.contains
    if ready.isEmpty then throwError "cake_program: cyclic dependencies between unit classes"
    for r in ready do
      placed := placed.insert r
      orderC := orderC.push r
    todoC := rest
  -- `CAKE_GROUP_SIZE` overrides the size (for testing the multi-group assembly)
  let groupSize := ((← IO.getEnv "CAKE_GROUP_SIZE").bind String.toNat?).getD 64
  let mut groupsI : Array (Array Nat) := #[]
  let mut cur : Array Nat := #[]
  for r in orderC do
    cur := cur ++ members.getD r #[]
    if cur.size ≥ groupSize then
      groupsI := groupsI.push cur
      cur := #[]
  unless cur.isEmpty do groupsI := groupsI.push cur
  let m := groupsI.size
  let mut groupOf : Std.HashMap Name Nat := {}
  for k in [0:m] do
    for i in groupsI[k]! do groupOf := groupOf.insert us[i]!.name k
  let entryOf (u : UnitInfo) : MetaM Expr := do
    let (param, body) := match u.kind with
      | .function p b _ => (p, b)
      | .thunk p b => (p, b)
    mkAppM ``Prod.mk #[mlString u.cname, ← mkAppM ``Prod.mk #[mlString param, mkConst body]]
  -- per group: the list `P.g_k`, membership of its entries, the binding lists
  let bindTy ← mkAppM ``Prod #[mkConst ``VarN, mkConst ``Value]
  let bindL ← mkAppM ``List #[bindTy]
  let gListTy ← mkAppM ``List #[fty]
  addDef (P ++ `L_0) bindL (mkApp (mkConst ``List.nil [0]) bindTy)
  let mut gConsts : Array Expr := #[]
  let mut lConsts : Array Expr := #[mkConst (P ++ `L_0)]
  let mut envs : Array Expr := #[]
  let mut gmem : Std.HashMap Name Expr := {}
  let mut gEntries : Array (Array Expr) := #[]
  let mut ents : Array (String × UnitInfo) := #[]
  for k in [0:m] do
    let es ← groupsI[k]!.mapM fun i => entryOf us[i]!
    let sfx := suffixes fty es
    let gn := P ++ Name.mkSimple s!"g_{k}"
    addDef gn gListTy sfx[0]!
    let g := mkConst gn
    let E := mkApp2 (mkConst ``flatEnv) envCc lConsts[k]!
    for j in [0:es.size] do
      let u := us[groupsI[k]![j]!]!
      let n := P ++ Name.mkSimple s!"gmem_{u.cname.drop 1}"
      addThmT n (← memTy fty es[j]! g) (memChain fty es sfx j)
      gmem := gmem.insert u.name (mkConst n)
      ents := ents.push (u.cname, u)
    let ln := P ++ Name.mkSimple s!"L_{k+1}"
    addDef ln bindL (← mkAppM ``HAppend.hAppend #[mkApp2 (mkConst ``groupBinds) g E, lConsts[k]!])
    gConsts := gConsts.push g
    lConsts := lConsts.push (mkConst ln)
    envs := envs.push E
    gEntries := gEntries.push es
  tick s!"{m} groups"
  -- distinctness of all names, in the order of the final binding list
  let mut lnames : Array String := #[]
  for k' in [0:m] do
    let k := m - 1 - k'
    for i in groupsI[k]! do lnames := lnames.push us[i]!.cname
  let sortedNames := lnames.qsort keyLt
  for i in [1:sortedNames.size] do
    unless keyLt sortedNames[i-1]! sortedNames[i]! do throwError "cake_program: duplicate unit name {sortedNames[i]!}"
  addDef (P ++ `lnames) llc (lit0 lc (lnames.toList.map charsE))
  let fuel := (Nat.log2 lnames.size) + 2
  let keys := mkApp4 (mkConst ``List.map [0, 0]) lc (mkApp (mkConst ``List [0]) (mkConst ``Nat)) (mkConst ``charKey)
    (mkConst (P ++ `lnames))
  let lkTy ← mkEq (mkApp (mkConst ``sortedN) (mkApp2 (mkConst ``msortF) (mkRawNatLit fuel) keys)) (mkConst ``Bool.true)
  addThmT (P ++ `lkeys) lkTy (← mkEqRefl (mkConst ``Bool.true))
  let fstB ← withLocalDeclD `p bindTy fun p => do mkLambdaFVars #[p] (← mkAppM ``Prod.fst #[p])
  let keysOf (L : Expr) : MetaM Expr := mkAppM ``List.map #[fstB, L]
  let xsM ← keysOf lConsts[m]!
  addThmT (P ++ Name.mkSimple s!"nodupL_{m}") (← mkAppM ``List.Nodup #[xsM])
    (mkAppN (mkConst ``nodup_names_msort) #[xsM, mkConst (P ++ `lnames), mkRawNatLit fuel, ← mkEqRefl xsM,
      mkConst (P ++ `lkeys)])
  let mut nodupL : Array Expr := Array.replicate (m + 1) (mkConst (P ++ Name.mkSimple s!"nodupL_{m}"))
  let mut nodupG : Array Expr := Array.replicate m (mkConst (P ++ Name.mkSimple s!"nodupL_{m}"))
  for k' in [0:m] do
    let k := m - 1 - k'
    let hk1 := nodupL[k+1]!
    let nL := P ++ Name.mkSimple s!"nodupL_{k}"
    addThmT nL (← mkAppM ``List.Nodup #[← keysOf lConsts[k]!])
      (mkAppN (mkConst ``nodup_rest_of) #[gConsts[k]!, envs[k]!, lConsts[k]!, hk1])
    nodupL := nodupL.set! k (mkConst nL)
    let fstFn ← withLocalDeclD `p fty fun p => do mkLambdaFVars #[p] (← mkAppM ``Prod.fst #[p])
    let nG := P ++ Name.mkSimple s!"nodupG_{k}"
    addThmT nG (← mkAppM ``List.Nodup #[← mkAppM ``List.map #[fstFn, gConsts[k]!]])
      (mkAppN (mkConst ``nodup_group_of) #[gConsts[k]!, envs[k]!, lConsts[k]!, hk1])
    nodupG := nodupG.set! k (mkConst nG)
  tick "distinctness"
  -- per unit: find and self-lookup in its group
  let mut lookups : Std.HashMap Name Expr := {}
  let mut finds : Std.HashMap Name Expr := {}
  for (cname, u) in ents do
    let some k := groupOf.get? u.name | unreachable!
    let some mem := gmem.get? u.name | unreachable!
    let (param, body) := match u.kind with
      | .function p b _ => (p, b)
      | .thunk p b => (p, b)
    let g := mlString cname
    let x := mlString param
    let b := mkConst body
    let tag := cname.drop 1
    let lkN := P ++ Name.mkSimple s!"lookup_{tag}"
    addThmT lkN (← groupLookupTy envs[k]! gConsts[k]! cname)
      (mkAppN (mkConst ``groupLookup_of_mem) #[gConsts[k]!, envs[k]!, g, x, b, mem])
    lookups := lookups.insert u.name (mkConst lkN)
    let findTy ← mkEq (← mkAppM ``findRecFun #[g, gConsts[k]!]) (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[x, b]])
    let findN := P ++ Name.mkSimple s!"find_{tag}"
    addThmT findN findTy
      (mkAppN (mkConst ``findRecFun_of_mem) #[mkConst ``VarN, mkConst ``Exp, gConsts[k]!, g, x, b, nodupG[k]!, mem])
    finds := finds.insert u.name (mkConst findN)
  tick "lookups"
  -- `(n_d, value of d) ∈ L_k` for a unit `d` of a group before `k`
  let valueOf (d : UnitInfo) : MetaM Expr := do
    let some j := groupOf.get? d.name | unreachable!
    mkAppM ``Value.recclosure #[envs[j]!, gConsts[j]!, mlString d.cname]
  let memL (d : UnitInfo) (k : Nat) : MetaM Expr := do
    let some j := groupOf.get? d.name | unreachable!
    let some mem := gmem.get? d.name | unreachable!
    let (param, body) := match d.kind with
      | .function p b _ => (p, b)
      | .thunk p b => (p, b)
    let a ← mkAppM ``Prod.mk #[mlString d.cname, ← valueOf d]
    let gb (i : Nat) := mkApp2 (mkConst ``groupBinds) gConsts[i]! envs[i]!
    let mut pf := mkAppN (mkConst ``mem_appL) #[bindTy, a, gb j, lConsts[j]!,
      mkAppN (mkConst ``mem_groupBinds) #[gConsts[j]!, envs[j]!, mlString d.cname, mlString param, mkConst body, mem]]
    for i in [j+1:k] do
      pf := mkAppN (mkConst ``mem_appR) #[bindTy, a, gb i, lConsts[i]!, pf]
    return pf
  -- certificates, in registration order, all under `h : RuntimeAssumptions`
  withLocalDeclD `h (mkConst ``ConPastel.RuntimeAssumptions) fun hrt => do
  let mut certs : Std.HashMap Name Expr := {}
  for u in us do
    let tag := u.cname.drop 1
    let some k := groupOf.get? u.name | unreachable!
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
    let mut args : Array Expr := #[envs[k]!, gConsts[k]!, nodupG[k]!, hfind, hbool, hlist] ++ hcs ++ #[lkC] ++ has
    for p in u.peers do
      unless groupOf.get? p == some k do throwError "peer {p} of {u.key} is in another group"
      let some pf := finds.get? p | throwError "peer {p} of {u.key} not assembled"
      let some pl := lookups.get? p | throwError "peer {p} of {u.key} not assembled"
      args := args ++ #[pf, pl]
    for d in depNamesOf env u do
      let some dc := certs.get? d | throwError "dependency {d} of {u.key} not assembled"
      let some du := byName.get? d | throwError "dependency {d} of {u.key} is not a unit"
      let some j := groupOf.get? d | unreachable!
      let dv ← valueOf du
      if j == k then
        let some dl := lookups.get? d | throwError "dependency {d} of {u.key} not assembled"
        args := args ++ #[dv, dl, dc]
      else
        unless j < k do throwError "dependency {d} of {u.key} is in a later group"
        let dl := mkAppN (mkConst ``depLookup) #[envCc, gConsts[k]!, lConsts[k]!, mlString du.cname, dv,
          nodupL[k+1]!, ← memL du k]
        args := args ++ #[dv, dl, dc]
    ConPastel.Translator.Meta.cakeLog s!"[cake_program] cert {u.name} ({args.size} args)"
    addThm (P ++ Name.mkSimple s!"cert_{tag}") (← mkLambdaFVars #[hrt] (mkAppN (mkConst u.cert) args))
    certs := certs.insert u.name (mkApp (mkConst (P ++ Name.mkSimple s!"cert_{tag}")) hrt)
  tick "certificates"
  -- the constructor-arity condition: one derivation per unit, then per group
  let cx : CokCtx := { tbl, mems }
  let mut cokU : Std.HashMap Name Expr := {}
  for (cname, u) in ents do
    let body := match u.kind with
      | .function _ b _ => b
      | .thunk _ b => b
    let some v := (← getConstInfo body).value? | throwError "{body} has no value"
    let (pf, _) ← (cokE cx v).run {}
    let n := P ++ Name.mkSimple s!"cok_{cname.drop 1}"
    addThmT n (mkApp2 (mkConst ``COk) tbl (mkConst body)) pf
    cokU := cokU.insert u.name (mkConst n)
  let mut hcons : Array Expr := #[]
  for k in [0:m] do
    let es := gEntries[k]!
    let sfx := suffixes fty es
    let mut p := mkApp (mkConst ``COkF.nil) tbl
    for j' in [0:es.size] do
      let j := es.size - 1 - j'
      let u := us[groupsI[k]![j]!]!
      let (``Prod.mk, #[_, _, f, r]) := es[j]!.getAppFnArgs | unreachable!
      let (``Prod.mk, #[_, _, x, e]) := r.getAppFnArgs | unreachable!
      let some hu := cokU.get? u.name | unreachable!
      p := mkAppN (mkConst ``COkF.cons) #[tbl, f, x, e, sfx[j+1]!, hu, p]
    let n := P ++ Name.mkSimple s!"cokG_{k}"
    addThmT n (mkApp2 (mkConst ``COkF) tbl gConsts[k]!) p
    let conOkPf := mkAppN (mkConst ``conOkFuns_of_COkF) #[tbl, mkConst (P ++ `tblNodup), gConsts[k]!, mkConst n]
    hcons := hcons.push (mkAppN (mkConst ``group_conOk_of) #[envC, cl, hc, gConsts[k]!, conOkPf])
  tick "constructor arities"
  -- the program and its correctness
  let gsTy ← mkAppM ``List #[gListTy]
  addDef (P ++ `gs) gsTy (lit0 gListTy gConsts.toList)
  let gs := mkConst (P ++ `gs)
  let gsSfx := suffixes gListTy gConsts
  let mut hok := mkApp (mkConst ``GroupsOk.nil) envCc
  for k' in [0:m] do
    let k := m - 1 - k'
    hok := mkAppN (mkConst ``GroupsOk.cons) #[envCc, gConsts[k]!, gsSfx[k+1]!, nodupG[k]!, hcons[k]!, hok]
  addThmT (P ++ `hok) (mkApp2 (mkConst ``GroupsOk) envCc gs) hok
  let hLmTy ← mkEq (mkApp3 (mkConst ``bindsAfter) envCc gs (mkConst (P ++ `L_0))) lConsts[m]!
  addThmT (P ++ `hLm) hLmTy (← mkEqRefl lConsts[m]!)
  let mainDecs ← mkAppM ``ConPastel.Main.mainDecs #[toExpr eu.cname, toExpr ru.cname]
  let loc := mkConst ``Flapjack.Misc.Location.unknownLoc
  let dletrecs ← mkAppM ``List.map #[mkApp (mkConst ``Dec.dletrec) loc, gs]
  let prog ← mkAppM ``List.cons #[← mkAppM ``Dec.dtype #[loc, tds], ← mkAppM ``HAppend.hAppend #[dletrecs, mainDecs]]
  addDef (P ++ `prog) (← mkAppM ``List #[mkConst ``Dec]) prog
  let lookupFinal (u : UnitInfo) : MetaM Expr := do
    return mkAppN (mkConst ``lookup_flat) #[lConsts[m]!, mlString u.cname, ← valueOf u, nodupL[m]!, ← memL u m]
  let ne (a b : String) : MetaM Expr := do closeWith (mkNot (← mkEq (mlString a) (mlString b))) (← `(tactic| decide))
  let some ce := certs.get? eu.name | unreachable!
  let some cr := certs.get? ru.name | unreachable!
  let pf ← mkAppOptM ``program_completes_groups #[tds, gs, lConsts[m]!, mkConst (P ++ `hLm),
    toExpr eu.cname, toExpr ru.cname, mkConst entry, hdup, mkConst (P ++ `hok),
    ← valueOf eu, ← valueOf ru, ← lookupFinal eu, ce, ← lookupFinal ru, cr, hlist,
    ← ne eu.cname ConPastel.Main.bufName, ← ne eu.cname ConPastel.Main.readAllName,
    ← ne ru.cname ConPastel.Main.bufName, ← ne ru.cname ConPastel.Main.readAllName]
  addThm (P ++ `correct) (← mkLambdaFVars #[hrt] pf)
  tick "correct"

elab "cake_program " P:ident entry:ident : command => do
  let e ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo entry
  liftTermElabM <| cakeProgram P.getId e

end ConPastel.Program
