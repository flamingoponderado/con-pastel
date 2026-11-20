import Lean
import ConPastel.Translator.Lemmas
import ConPastel.Translator.Tuple
import ConPastel.Translator.Meta.Ext
import ConPastel.Translator.List
import ConPastel.Translator.Braun
import ConPastel.Translator.EvalM

/-!
# The proof-producing translator: expressions

`transExpr ctx e` returns a CakeML expression `ce` and a proof of
`Eval ctx.env ce (INV e)`, where `INV` is the refinement invariant of `e`'s
type. The proof is built by chaining the lemmas of `ConPastel.Translator`.
-/

namespace ConPastel.Translator.Meta
open Lean Meta Elab
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- A Lean local in scope, with the CakeML variable holding its value. -/
structure LocalVar where
  fvar : Expr
  cname : String
  value : Expr
  inv : Expr
  rel : Expr

/-- A translated global: a CakeML variable bound (in every environment the
translator works in) to `value`, with certificate `cert : inv const value`. -/
structure GlobalVar where
  cname : String
  value : Expr
  inv : Expr
  cert : Expr

structure Ctx where
  /-- The current environment, a `SemEnv Value` term. -/
  env : Expr
  /-- Proof of `HasBoolCons env.c`. -/
  hbool : Expr
  locals : Array LocalVar := #[]
  /-- Globals, keyed by Lean constant. Lookups go through `globalLookup`. -/
  globals : NameMap GlobalVar := {}
  /-- Proof builder for global lookups: given the CakeML name, a proof of
  `nsLookup env.v (.short name) = some value`. -/
  globalLookup : String → MetaM Expr := fun n => throwError "no global {n}"

abbrev TransM := ReaderT Ctx MetaM

def mlString (s : String) : Expr :=
  mkApp (mkConst ``Flapjack.Basis.Pure.MlString.ofString) (toExpr s)

def shortIdent (s : String) : Expr :=
  mkApp3 (mkConst ``Ident.short) (mkConst ``ModN) (mkConst ``VarN) (mlString s)

/-! ## Invariants -/

/-- Is the field type erased (a proof or a type)? -/
def isErasedType (ty : Expr) : MetaM Bool := do
  return (← isProp ty) || (← isTypeFormerType ty)

/-- The element type of an array represented by a Braun tree (`NEWTYPE toA`):
every `Array α` except `Array UInt8` (byte arrays and strings stay lists). -/
def treeArrayElem? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnfR ty
  if ty.isAppOfArity ``Array 1 then
    let α := ty.appArg!
    if (← whnfR α).isConstOf ``UInt8 then return none
    if α.hasLooseBVars then return none
    -- the tree library is at `Type`
    unless (← getLevel α) == levelOne do return none
    return some α
  return none

/-- A structure type with exactly one data field: `(I, j, fieldType)`, the
field's index and type (with the other fields abstracted as projections). -/
def newtypeInfo? (ty : Expr) : MetaM (Option (Name × Nat × Expr)) := do
  let ty ← whnfR ty
  -- `UInt64` is a CakeML word (`UINT64`), not its `BitVec` field
  if ty.isConstOf ``UInt64 then return none
  -- arrays are Braun trees (`treeArrayElem?`), not their list field
  if (← treeArrayElem? ty).isSome then return none
  let .const I lvls := ty.getAppFn | return none
  let some (.inductInfo ii) := (← getEnv).find? I | return none
  unless ii.ctors.length == 1 && ii.numIndices == 0 && !ii.isRec do return none
  let params := ty.getAppArgs
  unless params.size == ii.numParams do return none
  let ctorTy ← instantiateTypeLevelParams (← getConstInfo ii.ctors.head!).toConstantVal lvls
  let ctorTy ← instantiateForall ctorTy params
  forallTelescope ctorTy fun fs _ => do
    let mut data : Array Nat := #[]
    for i in [0:fs.size] do
      unless ← isErasedType (← inferType fs[i]!) do data := data.push i
    unless data.size == 1 do return none
    let j := data[0]!
    let fty ← inferType fs[j]!
    if fty.hasAnyFVar (fs.contains <| .fvar ·) then return none
    return some (I, j, fty)

/-- A type with its reducible abbreviations unfolded throughout (`Unit` is
`PUnit`, …): datatypes are registered and looked up by this normal form. -/
def normType (ty : Expr) : MetaM Expr := do
  Meta.transform (← instantiateMVars ty) (post := fun e => do
    let e' ← whnfR e
    if e' != e then return .visit e' else return .done e)

/-- The registered datatype for `ty` (up to `normType`). -/
def findDatatype? (ty : Expr) : MetaM (Option DatatypeInfo) := do
  return getDatatypeByType? (← getEnv) (← normType ty)

/-- `StateT σ (Except ε) α` with `σ` a registered state type (`cake_state_ref`):
`(σ, ε, α)`. -/
def stateRefMonad? (ty : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let ty ← instantiateMVars ty
  unless ty.isAppOfArity ``StateT 3 do return none
  let #[σ, m, α] := ty.getAppArgs | return none
  let .const sc _ := (← whnfR σ).getAppFn | return none
  unless (stateRefExt.getState (← getEnv)).contains sc do return none
  let m ← whnfR m
  unless m.isAppOfArity ``Except 1 do return none
  return some (σ, m.appArg!, α)

/-- `StateT (Array T) (Except ε) α` with `T` a registered array-state element
type (`cake_state_array`): `(T, ε, α)`. -/
def stateArrMonad? (ty : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let ty ← instantiateMVars ty
  unless ty.isAppOfArity ``StateT 3 do return none
  let #[σ, m, α] := ty.getAppArgs | return none
  let σ ← whnfR σ
  unless σ.isAppOfArity ``Array 1 do return none
  let .const ec _ := (← whnfR σ.appArg!).getAppFn | return none
  unless (stateArrExt.getState (← getEnv)).contains ec do return none
  let m ← whnfR m
  unless m.isAppOfArity ``Except 1 do return none
  return some (σ.appArg!, m.appArg!, α)

partial def invOf (ty : Expr) : MetaM Expr := do
  if let some (el, ε, α) ← stateArrMonad? ty then
    let invE ← invOf el
    let rf ← withLocalDeclD `loc (mkConst ``Nat) fun loc => do
      mkLambdaFVars #[loc] (← mkAppM ``ConPastel.Translator.arrRel #[invE, loc])
    return ← mkAppOptM ``ConPastel.Translator.MRET #[← mkAppM ``Array #[el], ε, α, rf, ← invOf α, ← invOf ε]
  if let some (σ, ε, α) ← stateRefMonad? ty then
    let invS ← invOf σ
    let rf ← withLocalDeclD `loc (mkConst ``Nat) fun loc => do
      mkLambdaFVars #[loc] (← mkAppM ``ConPastel.Translator.refRel #[invS, loc])
    return ← mkAppOptM ``ConPastel.Translator.MRET #[σ, ε, α, rf, ← invOf α, ← invOf ε]
  let ty ← whnfR (← instantiateMVars ty).headBeta
  -- `Id α` is `α` (`Id` is only `implicit_reducible`)
  if ty.isAppOfArity ``Id 1 then return ← invOf ty.appArg!
  if ty.isConstOf ``Nat then return mkConst ``NAT
  if ty.isConstOf ``Int then return mkConst ``INT
  if ty.isConstOf ``Bool then return mkConst ``BOOL
  if ty.isConstOf ``UInt64 then return mkConst ``UINT64
  if ty.isConstOf ``Unit || ty.isAppOfArity ``PUnit 0 then return mkConst ``UNIT
  if let .const c [] := ty then
    if (ghostExt.getState (← getEnv)).contains c then return ← mkAppM ``GHOST #[ty]
  if ty.isAppOfArity ``List 1 then
    return ← mkAppM ``LIST #[← invOf ty.appArg!]
  if ty.isAppOfArity ``Quot 2 then
    return ← mkAppOptM ``QUOT #[ty.appFn!.appArg!, ty.appArg!, ← invOf ty.appFn!.appArg!]
  if ty.isAppOfArity ``Prod 2 then
    return ← mkAppM ``PAIR #[← invOf ty.appFn!.appArg!, ← invOf ty.appArg!]
  if let some α ← treeArrayElem? ty then
    let aTy := mkApp (mkConst ``ConPastel.Braun.A []) α
    let proj := mkApp (mkConst ``ConPastel.Braun.toA []) α
    return ← mkAppOptM ``NEWTYPE #[ty, aTy, proj, ← invOf aTy]
  if let some (I, j, fty) ← newtypeInfo? ty then
    let proj ← withLocalDeclD `s ty fun x => mkLambdaFVars #[x] (.proj I j x)
    return ← mkAppOptM ``NEWTYPE #[ty, fty, proj, ← invOf fty]
  -- datatypes (instances of closed inductive types)
  if let .const I _ := ty.getAppFn then
    if let some (.inductInfo _) := (← getEnv).find? I then
      if !ty.hasFVar && !ty.hasMVar then
        if let some d ← findDatatype? ty then return mkConst (d.name ++ `cakeInv)
        let nty ← normType ty
        needDatatypeRef.set (some nty)
        needDatatypesAllRef.modify (·.push nty)
        throwError "cake: need datatype {ty}"
  if let .forallE n a b bi := ty then
    -- a leading proof argument: the value exists regardless
    if ← isProp a then
      let β ← withLocalDecl n bi a fun h => do mkLambdaFVars #[h] (b.instantiate1 h)
      let invB ← withLocalDecl n bi a fun h => do mkLambdaFVars #[h] (← invOf (b.instantiate1 h))
      return ← mkAppOptM ``PIPROP #[a, β, invB]
    -- a data argument followed by a proof about it
    let dp? ← withLocalDecl n bi a fun x => do
      let b' ← whnfR (b.instantiate1 x)
      if let .forallE hn p rest hbi := b' then
        if ← isProp p then
          let P ← mkLambdaFVars #[x] p
          let β ← withLocalDecl hn hbi p fun h => do mkLambdaFVars #[x, h] (rest.instantiate1 h)
          let invB ← withLocalDecl hn hbi p fun h => do mkLambdaFVars #[x, h] (← invOf (rest.instantiate1 h))
          return some (P, β, invB)
      return none
    if let some (P, β, invB) := dp? then
      return ← mkAppOptM ``DARROWP #[a, P, β, ← invOf a, invB]
    if b.hasLooseBVars then
      let invA ← invOf a
      let invB ← withLocalDecl n bi a fun x => do mkLambdaFVars #[x] (← invOf (b.instantiate1 x))
      let β ← withLocalDecl n bi a fun x => do mkLambdaFVars #[x] (b.instantiate1 x)
      return ← mkAppOptM ``DARROW #[a, β, invA, invB]
    return ← mkAppM ``Arrow #[← invOf a, ← invOf b]
  -- type-level definitions (`StateT σ m α`, monad abbreviations, …): unfold
  if let .const c _ := ty.getAppFn then
    if let some (.defnInfo _) := (← getEnv).find? c then
      if let some ty' ← unfoldDefinition? ty then
        return ← invOf ty'
  throwError "no refinement invariant for type {ty}"

/-! ## Variable lookups -/

/-- Prove `nsLookup env.v (.short n) = some v` by unfolding the binds. -/
def proveLookup (env : Expr) (n : String) (v : Expr) : MetaM Expr := do
  let goal ← mkEq (← mkAppM ``nsLookup #[← mkAppM ``SemEnv.v #[env], shortIdent n])
    (← mkAppM ``Option.some #[v])
  let mvar ← mkFreshExprMVar goal
  let stx ← `(tactic| simp (config := { decide := true }) only
      [nsLookup_nsBind_short, nsOptBind, ite_true, ite_false, SemEnv.v])
  let remaining ← Tactic.run mvar.mvarId! (Tactic.evalTactic stx) |>.run'
  unless remaining.isEmpty do
    throwError "lookup of {n} not proved: {remaining.map (·.name)}"
  instantiateMVars mvar

/-! ## Expressions -/

/-- Fresh CakeML variable names. -/
def freshName (ctx : Ctx) : String := s!"v{ctx.locals.size}"

mutual

partial def transExpr (e : Expr) : TransM (Expr × Expr) := do
  let ctx ← read
  let e ← instantiateMVars e
  -- locals
  if e.isFVar then
    let some lv := ctx.locals.find? (·.fvar == e) | throwError "unknown local {e}"
    let hl ← proveLookup ctx.env lv.cname lv.value
    let ce := mkApp (mkConst ``Exp.var) (shortIdent lv.cname)
    let pf ← mkAppOptM ``Eval_var #[ctx.env, shortIdent lv.cname, lv.value, mkApp lv.inv e, hl, lv.rel]
    return (ce, pf)
  -- Nat literals
  if let some n := (← instantiateMVars e).nat? then
    if (← whnfR (← inferType e)).isConstOf ``Nat then
      let ce ← mkAppM ``Exp.lit #[← mkAppM ``Lit.intLit #[← mkAppM ``Int.ofNat #[toExpr n]]]
      let pf ← mkAppM ``Eval_nat_lit #[ctx.env, toExpr n]
      return (ce, pf)
  if e.isRawNatLit then
    let n := e.rawNatLit?.get!
    let ce ← mkAppM ``Exp.lit #[← mkAppM ``Lit.intLit #[← mkAppM ``Int.ofNat #[toExpr n]]]
    let pf ← mkAppM ``Eval_nat_lit #[ctx.env, toExpr n]
    return (ce, pf)
  -- booleans
  if e.isConstOf ``Bool.true || e.isConstOf ``Bool.false then
    let b := e.isConstOf ``Bool.true
    let ce ← mkAppM ``boolLit #[toExpr b]
    let pf ← mkAppOptM ``Eval_bool_lit #[ctx.env, ctx.hbool, toExpr b]
    return (ce, pf)
  match e with
  | .letE n ty v b _ => transLet n ty v b
  | .lam n ty b bi => transLam n ty b bi
  | .mdata _ e' => transExpr e'
  | _ => transApp e

partial def transLet (n : Name) (ty v b : Expr) : TransM (Expr × Expr) := do
  let ctx ← read
  let (cv, pv) ← transExpr v
  let inv ← invOf ty
  let cname := freshName ctx
  withLocalDeclD n ty fun x => do
  withLocalDeclD `xv (mkConst ``Value) fun xv => do
  withLocalDeclD `hx (mkApp2 inv x xv) fun hx => do
    let env' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsOptBind #[← mkAppM ``Option.some #[mlString cname], xv,
      ← mkAppM ``SemEnv.v #[ctx.env]], ← mkAppM ``SemEnv.c #[ctx.env]]
    let lv : LocalVar := { fvar := x, cname, value := xv, inv, rel := hx }
    let (cb, pb) ← withReader (fun c => { c with env := env', locals := c.locals.push lv })
      (transExpr (b.instantiate1 x))
    -- Eval_let needs ∀ v, P v → Eval env' b Q with P = inv v-term; we
    -- instantiate x := v (the Lean value) and quantify over the CakeML value.
    let body ← mkLambdaFVars #[xv, hx] pb
    let bodyAtV := (← mkLambdaFVars #[x] body).beta #[v]
    let ce ← mkAppM ``Exp.let_ #[← mkAppM ``Option.some #[mlString cname], cv, cb]
    let pf ← mkAppOptM ``Eval_let #[none, none, none, none, none, none, pv, bodyAtV]
    return (ce, pf)

partial def transLam (n : Name) (ty b : Expr) (_bi : BinderInfo) : TransM (Expr × Expr) := do
  let ctx ← read
  let inv ← invOf ty
  let cname := freshName ctx
  withLocalDeclD n ty fun x => do
  withLocalDeclD `xv (mkConst ``Value) fun xv => do
  withLocalDeclD `hx (mkApp2 inv x xv) fun hx => do
    let env' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsBind #[mlString cname, xv, ← mkAppM ``SemEnv.v #[ctx.env]],
      ← mkAppM ``SemEnv.c #[ctx.env]]
    let lv : LocalVar := { fvar := x, cname, value := xv, inv, rel := hx }
    let (cb, pb) ← withReader (fun c => { c with env := env', locals := c.locals.push lv })
      (transExpr (b.instantiate1 x))
    let h ← mkLambdaFVars #[x, xv, hx] pb
    let ce ← mkAppM ``Exp.fn #[mlString cname, cb]
    let pf ← mkAppOptM ``Eval_fn_arrow #[none, none, none, none, none, none, none, none, h]
    return (ce, pf)

/-- Translate a decidable proposition to a CakeML boolean expression, with a
proof of `Eval env ce (BOOL (decide p))` for the given instance. -/
partial def transDecide (p : Expr) : TransM (Expr × Expr) := do
  let p ← whnfR p
  match p.getAppFnArgs with
  | (``LT.lt, #[ty, _, a, b]) =>
    if (← whnfR ty).isConstOf ``Nat then
      let (ca, pa) ← transExpr a
      let (cb, pb) ← transExpr b
      return (← mkAppM ``Exp.app #[mkConst ``Op.test |>.app (← mkAppM ``Test.compare #[mkConst ``Flapjack.Opb.lt])
          |>.app (mkConst ``PrimType.intT), ← mkListLit (mkConst ``Exp) [ca, cb]],
        ← mkAppM ``Eval_nat_lt #[pa, pb])
    throwError "unsupported comparison {p}"
  | (``LE.le, #[ty, _, a, b]) =>
    if (← whnfR ty).isConstOf ``Nat then
      let (ca, pa) ← transExpr a
      let (cb, pb) ← transExpr b
      return (← mkAppM ``Exp.app #[mkConst ``Op.test |>.app (← mkAppM ``Test.compare #[mkConst ``Flapjack.Opb.leq])
          |>.app (mkConst ``PrimType.intT), ← mkListLit (mkConst ``Exp) [ca, cb]],
        ← mkAppM ``Eval_nat_le #[pa, pb])
    throwError "unsupported comparison {p}"
  | (``Eq, #[ty, a, b]) =>
    if (← whnfR ty).isConstOf ``Nat then
      let (ca, pa) ← transExpr a
      let (cb, pb) ← transExpr b
      return (← mkAppM ``Exp.app #[mkConst ``Op.equality, ← mkListLit (mkConst ``Exp) [ca, cb]],
        ← mkAppM ``Eval_nat_eq #[pa, pb])
    throwError "unsupported equality {p}"
  | _ => throwError "unsupported proposition {p}"

partial def transApp (e : Expr) : TransM (Expr × Expr) := do
  let ctx ← read
  let fn := e.getAppFn
  let args := e.getAppArgs
  -- if-then-else
  if fn.isConstOf ``ite && args.size == 5 then
    let (cc, pc) ← transDecide args[1]!
    let (ct, pt) ← withLocalDeclD `h args[1]! fun h => do
      let (ct, pt) ← transExpr args[3]!
      return (ct, ← mkLambdaFVars #[h] pt)
    let (cf, pf) ← withLocalDeclD `h (mkNot args[1]!) fun h => do
      let (cf, pf) ← transExpr args[4]!
      return (cf, ← mkLambdaFVars #[h] pf)
    let ce ← mkAppM ``Exp.if_ #[cc, ct, cf]
    let inv ← invOf args[0]!
    let pf ← mkAppOptM ``Eval_ite #[args[0]!, inv, ctx.env, args[1]!, args[2]!, none, none, none,
      args[3]!, args[4]!, pc, pt, pf]
    return (ce, pf)
  -- Nat arithmetic (after unfolding instances)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[ty, _, _, _, a, b]) | (``HMul.hMul, #[ty, _, _, _, a, b]) =>
    if (← whnfR ty).isConstOf ``Nat then
      let isAdd := e.isAppOf ``HAdd.hAdd
      let (ca, pa) ← transExpr a
      let (cb, pb) ← transExpr b
      let op ← mkAppM ``Op.arith #[mkConst (if isAdd then ``Arith.add else ``Arith.mul), mkConst ``PrimType.intT]
      let ce ← mkAppM ``Exp.app #[op, ← mkListLit (mkConst ``Exp) [ca, cb]]
      let pf ← mkAppM (if isAdd then ``Eval_nat_add else ``Eval_nat_mul) #[pa, pb]
      return (ce, pf)
  | _ => pure ()
  -- applications of locals and globals
  if fn.isFVar || fn.isConst then
    let (cf, pf₀) ← transHead fn
    let mut ce := cf
    let mut pf := pf₀
    for a in args do
      let (ca, pa) ← transExpr a
      ce ← mkAppM ``Exp.app #[mkConst ``Op.opapp, ← mkListLit (mkConst ``Exp) [ce, ca]]
      pf ← mkAppM ``Eval_app_arrow #[pf, pa]
    return (ce, pf)
  throwError "cannot translate {e}"

partial def transHead (fn : Expr) : TransM (Expr × Expr) := do
  let ctx ← read
  if fn.isFVar then return ← transExpr fn
  let .const c _ := fn | throwError "bad head {fn}"
  let some g := ctx.globals.find? c | throwError "constant {c} has not been translated"
  let hl ← ctx.globalLookup g.cname
  let ce := mkApp (mkConst ``Exp.var) (shortIdent g.cname)
  let pf ← mkAppOptM ``Eval_var #[ctx.env, shortIdent g.cname, g.value, mkApp g.inv fn, hl, g.cert]
  return (ce, pf)

end

end ConPastel.Translator.Meta
