import Lean
import ConPastel.Translator.Lemmas
import ConPastel.Translator.Meta.Core

/-!
# The proof-producing translator, goal-directed

The translator works backwards on goals `Eval env ?ce (INV t)`: it picks the
lemma for the head of the Lean term `t`, and the lemma's conclusion fixes the
CakeML expression `?ce` by unification. Binders are entered with fresh
locals, so the expression metavariables (created outside) never depend on
them.
-/

namespace ConPastel.Translator.Meta
open Lean Meta Elab
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

structure GLVar where
  fvar : Expr
  cname : String
  value : Expr
  rel : Expr

/-- The function whose body is being translated, when it is recursive. -/
structure RecFn where
  /-- Head constant of the Lean function. -/
  head : Name
  /-- Static (non-recursive) arguments it is applied to. -/
  static : Array Expr
  /-- The induction hypothesis: `∀ y, r y x → ∀ yv, A y yv → AppReturns cl yv (B (f y))`. -/
  ih : Expr
  /-- The recursive closure value and its CakeML name. -/
  cl : Expr
  cname : String

structure GCtx where
  hbool : Expr
  globals : NameMap GlobalVar := {}
  globalLookup : Expr → String → MetaM Expr := fun _ n => throwError "no global {n}"
  rec? : Option RecFn := none

structure GSt where
  locals : Array GLVar := #[]
  fresh : Nat := 0

abbrev GoalM := StateRefT GSt (ReaderT GCtx MetaM)

def freshCName (pfx : String := "v") : GoalM String := do
  let s ← get
  set { s with fresh := s.fresh + 1 }
  return s!"{pfx}{s.fresh}"

/-- The simp set for variable lookups. -/
def lookupSimp : MetaM Syntax.Tactic :=
  `(tactic| simp (config := { decide := true }) only [nsLookup_nsBind_short, nsOptBind, ite_true,
      ite_false, SemEnv.v, recBodyEnv, buildRecEnv, List.foldr_cons, List.foldr_nil])

def proveLookupG (env : Expr) (n : String) (v : Expr) : MetaM Expr := do
  let goal ← mkEq (← mkAppM ``nsLookup #[← mkAppM ``SemEnv.v #[env], shortIdent n])
    (← mkAppM ``Option.some #[v])
  let mvar ← mkFreshExprMVar goal
  let remaining ← Tactic.run mvar.mvarId! (Tactic.evalTactic (← lookupSimp)) |>.run'
  unless remaining.isEmpty do
    throwError "lookup of {n} not proved"
  instantiateMVars mvar

/-- Run a tactic to close a side goal. -/
def closeWith (goal : Expr) (tac : Syntax.Tactic) : MetaM Expr := do
  let mvar ← mkFreshExprMVar goal
  let remaining ← Tactic.run mvar.mvarId! (Tactic.evalTactic tac) |>.run'
  unless remaining.isEmpty do
    throwError "side goal not closed: {goal}"
  instantiateMVars mvar

/-- Destructure a goal `Eval env ce P` into `(env, P)`. -/
def evalGoalParts (g : MVarId) : MetaM (Expr × Expr) := do
  let ty ← instantiateMVars (← g.getType)
  let ty := ty.headBeta
  match ty.getAppFnArgs with
  | (``Eval, #[env, _, p]) => return (env, p)
  | _ => throwError "not an Eval goal: {ty}"

def evalGoalCe (g : MVarId) : MetaM Expr := do
  let ty := (← instantiateMVars (← g.getType)).headBeta
  match ty.getAppFnArgs with
  | (``Eval, #[_, ce, _]) => return ce
  | _ => throwError "not an Eval goal: {ty}"

/-- A fresh goal `Eval env ?ce P`. -/
def newEvalGoal (env p : Expr) : MetaM (Expr × MVarId) := do
  let ce ← mkFreshExprMVar (mkConst ``Exp)
  let g ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, p])
  return (ce, g.mvarId!)

/-- Close `g` with the proof `pf`, unifying types (this fixes `?ce`). -/
def assignProof (g : MVarId) (pf : Expr) : MetaM Unit := do
  let pty ← inferType pf
  unless ← isDefEq pty (← g.getType) do
    throwError "lemma does not fit goal:\n{pty}\nvs\n{← g.getType}"
  g.assign pf

/-- `B (f a)` with `B` and the Lean term split out of `P`. -/
def splitInv (p : Expr) : MetaM (Expr × Expr) := do
  let p ← instantiateMVars p
  match p with
  | .app inv t => return (inv, t)
  | _ => throwError "invariant application expected: {p}"

mutual

partial def solve (g : MVarId) : GoalM Unit := do
  let (env, p) ← evalGoalParts g
  let (inv, t) ← splitInv p
  let t := (← instantiateMVars t).headBeta
  let st ← get
  let ctx ← read
  -- locals
  if t.isFVar then
    let some lv := st.locals.find? (·.fvar == t) | throwError "unknown local {t}"
    let hl ← proveLookupG env lv.cname lv.value
    assignProof g (← mkAppOptM ``Eval_var #[env, shortIdent lv.cname, lv.value, p, hl, lv.rel])
    return
  -- literals
  if let some n := t.nat? then
    if inv.isConstOf ``NAT then
      assignProof g (← mkAppM ``Eval_nat_lit #[env, toExpr n])
      return
  if let some n := t.rawNatLit? then
    assignProof g (← mkAppM ``Eval_nat_lit #[env, toExpr n])
    return
  if t.isConstOf ``Bool.true || t.isConstOf ``Bool.false then
    assignProof g (← mkAppOptM ``Eval_bool_lit #[env, ctx.hbool, toExpr (t.isConstOf ``Bool.true)])
    return
  match t with
  | .letE n ty v b _ => solveLet g env inv n ty v b
  | .lam n ty b _ => solveLam g env inv n ty b
  | .mdata _ t' => solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, (← evalGoalCe g), mkApp inv t']))
  | _ => solveApp g env inv t

partial def solveLet (g : MVarId) (env inv : Expr) (n : Name) (ty v b : Expr) : GoalM Unit := do
  let cname ← freshCName
  let invV ← invOf ty
  let (_, gv) ← newEvalGoal env (mkApp invV v)
  solve gv
  let ceB ← mkFreshExprMVar (mkConst ``Exp)
  let pfB ← withLocalDeclD n ty fun x => do
    withLocalDeclD `heq (← mkEq x v) fun heq => do
    withLocalDeclD `xv (mkConst ``Value) fun xv => do
    withLocalDeclD `hx (mkApp2 invV x xv) fun hx => do
      let env' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsBind #[mlString cname, xv, ← mkAppM ``SemEnv.v #[env]],
        ← mkAppM ``SemEnv.c #[env]]
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env', ceB, mkApp inv (b.instantiate1 x)])
      modify fun s => { s with locals := s.locals.push { fvar := x, cname, value := xv, rel := hx } }
      solve gb.mvarId!
      modify fun s => { s with locals := s.locals.pop }
      mkLambdaFVars #[x, heq, xv, hx] (← instantiateMVars gb)
  let bfun ← withLocalDeclD n ty fun x => mkLambdaFVars #[x] (b.instantiate1 x)
  let pf ← mkAppOptM ``Eval_let_eq #[none, none, invV, inv, env, mlString cname, none, ceB, v, bfun,
    ← instantiateMVars (mkMVar gv), pfB]
  assignProof g pf

partial def solveLam (g : MVarId) (env inv : Expr) (n : Name) (ty b : Expr) : GoalM Unit := do
  let cname ← freshCName
  -- inv must be `Arrow A B`
  let inv ← whnfR inv
  let (``Arrow, #[_, _, invA, invB]) := inv.getAppFnArgs
    | throwError "function expected to have an Arrow invariant, got {inv}"
  let ceB ← mkFreshExprMVar (mkConst ``Exp)
  let h ← withLocalDeclD n ty fun x => do
    withLocalDeclD `xv (mkConst ``Value) fun xv => do
    withLocalDeclD `hx (mkApp2 invA x xv) fun hx => do
      let env' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsBind #[mlString cname, xv, ← mkAppM ``SemEnv.v #[env]],
        ← mkAppM ``SemEnv.c #[env]]
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env', ceB, mkApp invB (b.instantiate1 x)])
      modify fun s => { s with locals := s.locals.push { fvar := x, cname, value := xv, rel := hx } }
      solve gb.mvarId!
      modify fun s => { s with locals := s.locals.pop }
      mkLambdaFVars #[x, xv, hx] (← instantiateMVars gb)
  let f ← withLocalDeclD n ty fun x => mkLambdaFVars #[x] (b.instantiate1 x)
  assignProof g (← mkAppOptM ``Eval_fn_arrow #[none, none, invA, invB, env, mlString cname, ceB, f, h])

/-- Translate `decide c`: a goal `Eval env ?ce (BOOL (decide c))`. -/
partial def solveDecide (g : MVarId) (env c : Expr) : GoalM Unit := do
  let c ← whnfR c
  let binNat (lem : Name) (a b : Expr) : GoalM Unit := do
    let (_, ga) ← newEvalGoal env (mkApp (mkConst ``NAT) a)
    let (_, gb) ← newEvalGoal env (mkApp (mkConst ``NAT) b)
    solve ga; solve gb
    assignProof g (← mkAppM lem #[← instantiateMVars (mkMVar ga), ← instantiateMVars (mkMVar gb)])
  match c.getAppFnArgs with
  | (``LT.lt, #[ty, _, a, b]) => if (← whnfR ty).isConstOf ``Nat then return ← binNat ``Eval_nat_lt a b
  | (``LE.le, #[ty, _, a, b]) => if (← whnfR ty).isConstOf ``Nat then return ← binNat ``Eval_nat_le a b
  | (``Eq, #[ty, a, b]) => if (← whnfR ty).isConstOf ``Nat then return ← binNat ``Eval_nat_eq a b
  | _ => pure ()
  throwError "unsupported condition {c}"

partial def solveApp (g : MVarId) (env inv t : Expr) : GoalM Unit := do
  let ctx ← read
  let fn := t.getAppFn
  let args := t.getAppArgs
  -- matchers: unfold to casesOn
  if let .const fnName _ := fn then
    if (← Meta.isMatcher fnName) then
      let .const _ lvls := fn | unreachable!
      let mci ← getConstInfo fnName
      let t' := (mkAppN (← instantiateValueLevelParams mci lvls) args).headBeta
      let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, (← evalGoalCe g), mkApp inv t'.headBeta])
      return ← solve g'
  -- conditions as Bool
  if fn.isConstOf ``Decidable.decide && args.size == 2 then
    return ← solveDecide g env args[0]!
  -- if-then-else
  if fn.isConstOf ``ite && args.size == 5 then
    let (_, gc) ← newEvalGoal env (← mkAppOptM ``decide #[args[1]!, args[2]!])
    solveDecide gc env args[1]!
    let ce₁ ← mkFreshExprMVar (mkConst ``Exp)
    let ce₂ ← mkFreshExprMVar (mkConst ``Exp)
    let h₁ ← withLocalDeclD `h args[1]! fun h => do
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce₁, mkApp inv args[3]!])
      solve gb.mvarId!
      mkLambdaFVars #[h] (← instantiateMVars gb)
    let h₂ ← withLocalDeclD `h (mkNot args[1]!) fun h => do
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce₂, mkApp inv args[4]!])
      solve gb.mvarId!
      mkLambdaFVars #[h] (← instantiateMVars gb)
    assignProof g (← mkAppOptM ``Eval_ite #[args[0]!, inv, env, args[1]!, args[2]!, none, ce₁, ce₂,
      args[3]!, args[4]!, ← instantiateMVars (mkMVar gc), h₁, h₂])
    return
  -- Nat.casesOn with a non-dependent motive
  if fn.isConstOf ``Nat.casesOn && args.size == 4 then
    let n := args[1]!
    let mn ← freshCName
    let (_, gn) ← newEvalGoal env (mkApp (mkConst ``NAT) n)
    solve gn
    let cez ← mkFreshExprMVar (mkConst ``Exp)
    let ces ← mkFreshExprMVar (mkConst ``Exp)
    let hz ← withLocalDeclD `h (← mkEq n (mkNatLit 0)) fun h => do
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, cez, mkApp inv args[2]!])
      solve gb.mvarId!
      mkLambdaFVars #[h] (← instantiateMVars gb)
    let hs ← withLocalDeclD `m (mkConst ``Nat) fun m => do
      withLocalDeclD `h (← mkEq n (← mkAppM ``HAdd.hAdd #[m, mkNatLit 1])) fun h => do
      withLocalDeclD `mv (mkConst ``Value) fun mv => do
      withLocalDeclD `hm (mkApp2 (mkConst ``NAT) m mv) fun hm => do
        let env' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsBind #[mlString mn, mv, ← mkAppM ``SemEnv.v #[env]],
          ← mkAppM ``SemEnv.c #[env]]
        let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env', ces, mkApp inv (args[3]!.beta #[m])])
        modify fun s => { s with locals := s.locals.push { fvar := m, cname := mn, value := mv, rel := hm } }
        solve gb.mvarId!
        modify fun s => { s with locals := s.locals.pop }
        mkLambdaFVars #[m, h, mv, hm] (← instantiateMVars gb)
    assignProof g (← mkAppOptM ``Eval_nat_casesOn #[none, inv, env, none, cez, ces, mlString mn, n,
      args[2]!, args[3]!, ← instantiateMVars (mkMVar gn), hz, hs])
    return
  -- Nat arithmetic
  match t.getAppFnArgs with
  | (``HAdd.hAdd, #[ty, _, _, _, a, b]) | (``HMul.hMul, #[ty, _, _, _, a, b]) =>
    if (← whnfR ty).isConstOf ``Nat then
      let lem := if t.isAppOf ``HAdd.hAdd then ``Eval_nat_add else ``Eval_nat_mul
      let (_, ga) ← newEvalGoal env (mkApp (mkConst ``NAT) a)
      let (_, gb) ← newEvalGoal env (mkApp (mkConst ``NAT) b)
      solve ga; solve gb
      assignProof g (← mkAppM lem #[← instantiateMVars (mkMVar ga), ← instantiateMVars (mkMVar gb)])
      return
  | _ => pure ()
  -- recursive calls
  if let some r := ctx.rec? then
    if fn.isConstOf r.head && args.size == r.static.size + 1 then
      let y := args[r.static.size]!
      -- the IH at y: ∀ yv, A y yv → AppReturns cl yv (B (f y))
      let ihTy ← whnfR (← inferType r.ih)
      let .forallE _ _ body _ := ihTy | throwError "bad IH"
      let .forallE _ relTy _ _ := body.instantiate1 y | throwError "bad IH"
      let hdec ← closeWith relTy (← `(tactic| first
        | decreasing_tactic
        | (simp_wf; omega)
        | (simp only [InvImage, Nat.lt_eq] at *; omega)))
      let ihy := mkApp2 r.ih y hdec
      let ihyTy ← whnfR (← inferType ihy)
      let .forallE _ _ ihB _ := ihyTy | throwError "bad IH at y"
      let .forallE _ invAy _ _ := ihB | throwError "bad IH at y"
      let invA := invAy.appFn!.appFn!
      let (_, gx) ← newEvalGoal env (mkApp invA y)
      solve gx
      let hl ← proveLookupG env r.cname r.cl
      let clEq ← withLocalDeclD `w (mkConst ``Value) fun w => do mkLambdaFVars #[w] (← mkEq w r.cl)
      let hf ← mkAppOptM ``Eval_var #[env, shortIdent r.cname, r.cl, clEq, hl, ← mkEqRefl r.cl]
      assignProof g (← mkAppOptM ``Eval_app_ih #[none, none, invA, inv, env, none, none, r.cl, none, y,
        hf, ← instantiateMVars (mkMVar gx), ihy])
      return
  -- applications of locals and globals: peel the last argument
  if fn.isFVar || fn.isConst then
    if args.isEmpty then
      if fn.isConst then
        let .const c _ := fn | unreachable!
        let some gv := ctx.globals.find? c | throwError "constant {c} has not been translated"
        let hl ← ctx.globalLookup env gv.cname
        assignProof g (← mkAppOptM ``Eval_var #[env, shortIdent gv.cname, gv.value, mkApp gv.inv fn, hl, gv.cert])
        return
    else
      let fpart := mkAppN fn args.pop
      let x := args.back!
      let xty ← inferType x
      let invA ← invOf xty
      let (_, gf) ← newEvalGoal env (mkApp (← mkAppM ``Arrow #[invA, inv]) fpart)
      let (_, gx) ← newEvalGoal env (mkApp invA x)
      solve gf; solve gx
      assignProof g (← mkAppM ``Eval_app_arrow #[← instantiateMVars (mkMVar gf), ← instantiateMVars (mkMVar gx)])
      return
  throwError "cannot translate {t}"

end

end ConPastel.Translator.Meta
