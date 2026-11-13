import Lean
import ConPastel.Translator.Lemmas
import ConPastel.Translator.Tuple
import ConPastel.Translator.Meta.Core
import ConPastel.Translator.Meta.Ext
import ConPastel.Translator.Meta.Keys

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
  /-- Number of curried arguments after the static ones; when more than one,
  the recursive closure takes them as a nested tuple. -/
  arity : Nat := 1

structure GCtx where
  hbool : Expr
  /-- Proof of `HasListCons env.c`. -/
  hlist : Expr := default
  /-- For each registered datatype, a proof of `T.cakeHasCons env.c`. -/
  hasCons : NameMap Expr := {}
  globals : Std.HashMap Expr GlobalVar := {}
  globalLookup : Expr → String → MetaM Expr := fun _ n => throwError "no global {n}"
  rec? : Option RecFn := none
  /-- Unfold singleton recursive groups in lookups (the older commands). -/
  unfoldRec : Bool := true

structure GSt where
  locals : Array GLVar := #[]
  fresh : Nat := 0

abbrev GoalM := StateRefT GSt (ReaderT GCtx MetaM)

def getLevels (_args : Array Expr) : MetaM (List Level) := pure []

def freshCName (pfx : String := "v") : GoalM String := do
  let s ← get
  set { s with fresh := s.fresh + 1 }
  return s!"{pfx}{s.fresh}"

/-- The simp set for variable lookups. With `unfoldRec`, singleton
recursive groups are unfolded (`buildRecEnv`); otherwise lookups into the
recursive group come from hypotheses in context. -/
def lookupSimp (unfoldRec : Bool) : MetaM Syntax.Tactic :=
  if unfoldRec then
    `(tactic| simp (config := { decide := true }) only [*, nsLookup_nsBind_short, nsOptBind, ite_true,
      ite_false, SemEnv.v, recBodyEnv, buildRecEnv, List.foldr_cons, List.foldr_nil, clauseEnv,
      nsLookup_nsAppend_alist_short, List.zip_cons_cons, List.zip_nil_left, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.lookup, beq_eq_decide_of_decEq,
      decide_true, decide_false])
  else
    `(tactic| simp (config := { decide := true }) only [*, nsLookup_nsBind_short, nsOptBind, ite_true,
      ite_false, SemEnv.v, recBodyEnv, clauseEnv,
      nsLookup_nsAppend_alist_short, List.zip_cons_cons, List.zip_nil_left, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.lookup, beq_eq_decide_of_decEq,
      decide_true, decide_false])

def proveLookupG (env : Expr) (n : String) (v : Expr) (unfoldRec : Bool := true) : MetaM Expr := do
  let goal ← mkEq (← mkAppM ``nsLookup #[← mkAppM ``SemEnv.v #[env], shortIdent n])
    (← mkAppM ``Option.some #[v])
  let mvar ← mkFreshExprMVar goal
  let remaining ← Tactic.run mvar.mvarId! (Tactic.evalTactic (← lookupSimp unfoldRec)) |>.run'
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
    let hl ← proveLookupG env lv.cname lv.value ctx.unfoldRec
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
  | .proj I j sExp =>
    if let some (I', j', _) ← newtypeInfo? (← inferType sExp) then
      if I' == I && j' == j then
        let invS ← invOf (← inferType sExp)
        let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp invS sExp])
        return ← solve g'
    throwError "unsupported projection {t}"
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
  -- any other instance: `decide c` is the projection of the instance (a newtype)
  let t ← mkAppOptM ``Decidable.decide #[c, none]
  let _ := t
  throwError "unsupported condition {c}"

partial def solveCases (g : MVarId) (env inv : Expr) (tn : Name) (dt : DatatypeInfo)
    (lvls : List Level) (args : Array Expr) : GoalM Unit := do
  let ctx ← read
  let motive := args[0]!
  let major := args[1]!
  let alts := args[2:].toArray
  let dep ← withLocalDeclD `x (mkConst tn) fun x => do
    let b ← instantiateMVars (motive.beta #[x])
    return b.headBeta.containsFVar x.fvarId!
  if dep then throwError "dependent casesOn motive not supported"
  unless major.isFVar do
    -- bind the scrutinee first: `T.casesOn m e alts` is `let z := e; T.casesOn m z alts`
    let ty ← inferType major
    let letT := Expr.letE `z ty major (mkAppN (mkConst (tn ++ `casesOn) lvls) (#[motive, .bvar 0] ++ alts)) false
    let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv letT])
    return ← solve g'
  let st ← get
  let some lv := st.locals.find? (·.fvar == major) | throwError "unknown scrutinee {major}"
  let some hc := ctx.hasCons.find? tn | throwError "no constructor environment for {tn}"
  let invT := mkConst (tn ++ `cakeInv)
  let hl ← proveLookupG env lv.cname lv.value ctx.unfoldRec
  let he ← mkAppOptM ``Eval_var #[env, shortIdent lv.cname, lv.value, mkApp invT major, hl, lv.rel]
  let casesFn := (← getConstInfo (tn ++ `casesOn))
  let qfun ← withLocalDeclD `x (mkConst tn) fun x => do
    mkLambdaFVars #[x] (mkApp inv (mkAppN (mkConst (tn ++ `casesOn) lvls) (#[motive, x] ++ alts)))
  let _ := casesFn
  let mut lemArgs : Array (Option Expr) := #[some env, some hc, none, some major, some he, some qfun]
  for k in [0:dt.ctors.size] do
    let (c, n) := dt.ctors[k]!
    let ctorTy := (← getConstInfo c).type
    let fieldTys ← forallTelescope ctorTy fun fs _ => fs.mapM fun f => inferType f
    let names ← (List.range n).mapM fun _ => freshCName "f"
    let nameList ← mkListLit (mkConst ``VarN) (names.map mlString)
    let hnd ← closeWith (← mkAppM ``List.Nodup #[nameList]) (← `(tactic| decide))
    let bk ← mkFreshExprMVar (mkConst ``Exp)
    -- the branch: ∀ a.., major = c a.. → ∀ w.., I a w → ... → Eval (clauseEnv env ns ws) bk (Q (c a..))
    let hk ← withLocalDeclsDND (fieldTys.mapIdx fun i ty => (Name.mkSimple s!"a{i}", ty)) fun as => do
      withLocalDeclD `heq (← mkEq major (mkAppN (mkConst c lvls.tail) as)) fun heq => do
      withLocalDeclsDND (as.mapIdx fun i _ => (Name.mkSimple s!"w{i}", mkConst ``Value)) fun ws => do
      let invs ← fieldTys.mapM fun ty => (invOf ty : MetaM Expr)
      withLocalDeclsDND (as.mapIdx fun i a => (Name.mkSimple s!"hw{i}", mkApp2 invs[i]! a ws[i]!)) fun hws => do
        let wList ← mkListLit (mkConst ``Value) ws.toList
        let envK ← mkAppM ``clauseEnv #[env, nameList, wList]
        let branchT := (mkAppN alts[k]! as).headBeta
        let gb ← mkFreshExprMVar (← mkAppM ``Eval #[envK, bk, mkApp inv branchT])
        let saved := (← get).locals
        for i in [0:n] do
          let lv : GLVar := { fvar := as[i]!, cname := names[i]!, value := ws[i]!, rel := hws[i]! }
          modify fun s => { s with locals := s.locals.push lv }
        solve gb.mvarId!
        modify fun s => { s with locals := saved }
        mkLambdaFVars (as ++ #[heq] ++ ws ++ hws) (← instantiateMVars gb)
    lemArgs := lemArgs ++ names.toArray.map (some ∘ mlString) ++ #[some hnd, some bk, some hk]
  assignProof g (← mkAppOptM (tn ++ `cake_mat) lemArgs)

partial def solveListCases (g : MVarId) (env inv fn : Expr) (args : Array Expr) : GoalM Unit := do
  let ctx ← read
  let α := args[0]!
  let motive := args[1]!
  let major := args[2]!
  let nilAlt := args[3]!
  let consAlt := args[4]!
  let listTy ← mkAppM ``List #[α]
  let dep ← withLocalDeclD `x listTy fun x => do
    return (← instantiateMVars (motive.beta #[x])).headBeta.containsFVar x.fvarId!
  if dep then throwError "dependent List.casesOn motive not supported"
  unless major.isFVar do
    let letT := Expr.letE `z listTy major (mkAppN fn #[α, motive, .bvar 0, nilAlt, consAlt]) false
    let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv letT])
    return ← solve g'
  let st ← get
  let some lv := st.locals.find? (·.fvar == major) | throwError "unknown scrutinee {major}"
  let invA ← invOf α
  let invL ← mkAppM ``LIST #[invA]
  let hl ← proveLookupG env lv.cname lv.value ctx.unfoldRec
  let he ← mkAppOptM ``Eval_var #[env, shortIdent lv.cname, lv.value, mkApp invL major, hl, lv.rel]
  let qfun ← withLocalDeclD `x listTy fun x => do
    mkLambdaFVars #[x] (mkApp inv (mkAppN fn #[α, motive, x, nilAlt, consAlt]))
  -- nil branch
  let bn ← mkFreshExprMVar (mkConst ``Exp)
  let emptyN ← mkListLit (mkConst ``VarN) []
  let emptyV ← mkListLit (mkConst ``Value) []
  let hn ← withLocalDeclD `h (← mkEq major (← mkAppOptM ``List.nil #[α])) fun h => do
    let envN ← mkAppM ``clauseEnv #[env, emptyN, emptyV]
    let gb ← mkFreshExprMVar (← mkAppM ``Eval #[envN, bn, mkApp inv nilAlt])
    solve gb.mvarId!
    mkLambdaFVars #[h] (← instantiateMVars gb)
  -- cons branch
  let nx ← freshCName "h"
  let ny ← freshCName "t"
  let hne ← closeWith (mkNot (← mkEq (mlString nx) (mlString ny))) (← `(tactic| decide))
  let bc ← mkFreshExprMVar (mkConst ``Exp)
  let hc ← withLocalDeclD `a α fun a => withLocalDeclD `as listTy fun as => do
    withLocalDeclD `h (← mkEq major (← mkAppM ``List.cons #[a, as])) fun h => do
    withLocalDeclD `w0 (mkConst ``Value) fun w0 => withLocalDeclD `w1 (mkConst ``Value) fun w1 => do
    withLocalDeclD `hw0 (mkApp2 invA a w0) fun hw0 => withLocalDeclD `hw1 (mkApp2 invL as w1) fun hw1 => do
      let envC ← mkAppM ``clauseEnv #[env, ← mkListLit (mkConst ``VarN) [mlString nx, mlString ny],
        ← mkListLit (mkConst ``Value) [w0, w1]]
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[envC, bc, mkApp inv (consAlt.beta #[a, as]).headBeta])
      let saved := (← get).locals
      let la : GLVar := { fvar := a, cname := nx, value := w0, rel := hw0 }
      let las : GLVar := { fvar := as, cname := ny, value := w1, rel := hw1 }
      modify fun s => { s with locals := s.locals.push la |>.push las }
      solve gb.mvarId!
      modify fun s => { s with locals := saved }
      mkLambdaFVars #[a, as, h, w0, w1, hw0, hw1] (← instantiateMVars gb)
  assignProof g (← mkAppOptM ``list_cake_mat #[α, invA, env, ctx.hlist, none, major, he, qfun,
    bn, hn, mlString nx, mlString ny, hne, bc, hc])

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
  -- conditions as Bool: known comparisons, else the instance (a newtype)
  if fn.isConstOf ``Decidable.decide && args.size == 2 then
    let saved : Meta.SavedState ← (Meta.saveState : MetaM _)
    let st₀ ← get
    try return ← solveDecide g env args[0]!
    catch _ =>
      (saved.restore : MetaM Unit)
      set st₀
    let t' := Expr.proj ``Decidable 0 args[1]!
    let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
    return ← solve g'
  -- if-then-else
  if fn.isConstOf ``ite && args.size == 5 then
    let (_, gc) ← newEvalGoal env (mkApp (mkConst ``BOOL) (← mkAppOptM ``decide #[args[1]!, args[2]!]))
    solve gc
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
  -- newtypes: constructor, projection functions, casesOn
  if let .const cn _ := fn then
    if let some (.ctorInfo ci) := (← getEnv).find? cn then
      if let some (I, j, _) ← newtypeInfo? (← inferType t) then
        if I == ci.induct && args.size == ci.numParams + ci.numFields then
          let field := args[ci.numParams + j]!
          let invF ← invOf (← inferType field)
          let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp invF field])
          return ← solve g'
    if let some info ← getProjectionFnInfo? cn then
      if args.size == info.numParams + 1 then
        let some (.ctorInfo ci) := (← getEnv).find? info.ctorName | throwError "bad projection {cn}"
        let t' := mkAppN (.proj ci.induct info.i args[info.numParams]!) args[info.numParams + 1:].toArray
        let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
        return ← solve g'
    let tn := cn.getPrefix
    if cn == tn ++ `casesOn then
      if let some (.inductInfo ii) := (← getEnv).find? tn then
        if ii.ctors.length == 1 && ii.numIndices == 0 && args.size == ii.numParams + 3 then
          let major := args[ii.numParams + 1]!
          if (← newtypeInfo? (← inferType major)).isSome then
            let some (.ctorInfo ci) := (← getEnv).find? ii.ctors.head! | unreachable!
            let projs := (List.range ci.numFields).map fun i => Expr.proj tn i major
            let t' := (mkAppN args[ii.numParams + 2]! projs.toArray).headBeta
            let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
            return ← solve g'
  -- lists
  if fn.isConstOf ``List.nil && args.size == 1 then
    let (``LIST, #[_, invA]) := (← whnfR inv).getAppFnArgs | throwError "list without LIST invariant"
    assignProof g (← mkAppOptM ``Eval_nil #[args[0]!, invA, env, ctx.hlist])
    return
  if fn.isConstOf ``List.cons && args.size == 3 then
    let (``LIST, #[_, invA]) := (← whnfR inv).getAppFnArgs | throwError "list without LIST invariant"
    let (_, g₁) ← newEvalGoal env (mkApp invA args[1]!)
    let (_, g₂) ← newEvalGoal env (mkApp inv args[2]!)
    solve g₁; solve g₂
    assignProof g (← mkAppOptM ``Eval_cons #[args[0]!, invA, env, ctx.hlist, none, none, args[1]!, args[2]!,
      ← instantiateMVars (mkMVar g₁), ← instantiateMVars (mkMVar g₂)])
    return
  if fn.isConstOf ``List.casesOn && args.size == 5 then
    return ← solveListCases g env inv fn args
  -- constructors of registered datatypes
  if let .const cn _ := fn then
    if let some (.ctorInfo ci) := (← getEnv).find? cn then
      if (getDatatype? (← getEnv) ci.induct).isSome then
        let some hc := ctx.hasCons.find? ci.induct | throwError "no constructor environment for {ci.induct}"
        let fieldTys ← forallTelescope ci.type fun fs _ => fs.mapM fun f => inferType f
        let mut pfs : Array Expr := #[]
        for i in [0:args.size] do
          let (_, gi) ← newEvalGoal env (mkApp (← invOf fieldTys[i]!) args[i]!)
          solve gi
          pfs := pfs.push (← instantiateMVars (mkMVar gi))
        let n := args.size
        let lemArgs : Array (Option Expr) := #[some env, some hc] ++ Array.replicate n none ++
          Array.replicate n none ++ pfs.map some
        assignProof g (← mkAppOptM (cn ++ `cake_con) lemArgs)
        return
  -- casesOn of registered datatypes, with a non-dependent motive
  if let .const cn lvls := fn then
    let tn := cn.getPrefix
    if cn == tn ++ `casesOn then
      if let some dt := getDatatype? (← getEnv) tn then
        return ← solveCases g env inv tn dt lvls args
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
  -- pairs
  if fn.isConstOf ``Prod.mk && args.size == 4 then
    let (``PAIR, #[_, _, invA, invB]) := (← whnfR inv).getAppFnArgs
      | throwError "pair without a PAIR invariant: {inv}"
    let (_, ga) ← newEvalGoal env (mkApp invA args[2]!)
    let (_, gb) ← newEvalGoal env (mkApp invB args[3]!)
    solve ga; solve gb
    assignProof g (← mkAppM ``Eval_pair #[← instantiateMVars (mkMVar ga), ← instantiateMVars (mkMVar gb)])
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
    if fn.isConstOf r.head && args.size == r.static.size + r.arity &&
        (args[:r.static.size].toArray == r.static) then
      let ys := args[r.static.size:].toArray
      let y ← if r.arity == 1 then pure ys[0]! else
        ys.pop.foldrM (fun a acc => mkAppM ``Prod.mk #[a, acc]) ys.back!
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
      let hl ← proveLookupG env r.cname r.cl ctx.unfoldRec
      let clEq ← withLocalDeclD `w (mkConst ``Value) fun w => do mkLambdaFVars #[w] (← mkEq w r.cl)
      let hf ← mkAppOptM ``Eval_var #[env, shortIdent r.cname, r.cl, clEq, hl, ← mkEqRefl r.cl]
      assignProof g (← mkAppOptM ``Eval_app_ih #[none, none, invA, inv, env, none, none, r.cl, none, y,
        hf, ← instantiateMVars (mkMVar gx), ihy])
      return
  -- applications of locals and globals: peel the last argument
  -- unit value
  if t.isConstOf ``Unit.unit || t.isConstOf ``PUnit.unit then
    assignProof g (← mkAppM ``Eval_unit #[env])
    return
  -- constants translated as thunks: `c ()`
  if fn.isConst then
    if let some (key, dargs) ← splitKey t then
      if dargs.isEmpty then
        if let some u := getUnit? (← getEnv) key then
          if let .thunk _ _ := u.kind then
            let some gv := ctx.globals.get? key | throwError "constant {key} not in scope"
            let hl ← proveLookupG env gv.cname gv.value ctx.unfoldRec
            let tgt ← withLocalDeclD `u (mkConst ``Unit) fun x => mkLambdaFVars #[x] key
            let hf ← mkAppOptM ``Eval_var #[env, shortIdent gv.cname, gv.value, mkApp gv.inv tgt, hl, gv.cert]
            let hx ← mkAppM ``Eval_unit #[env]
            assignProof g (← mkAppM ``Eval_app_arrow #[hf, hx])
            return
  -- fully applied tupled global units: call the tupled closure with a tuple
  if fn.isConst then
    if let some (key, dargs) ← splitKey t then
      if let some u := getUnit? (← getEnv) key then
        if let .function _ _ true := u.kind then
          let tupFn := mkConst (u.name ++ `tupled)
          let arity ← forallTelescope (← inferType key) fun xs _ => pure xs.size
          if dargs.size == arity then
            let tup ← dargs.pop.foldrM (fun a acc => mkAppM ``Prod.mk #[a, acc]) dargs.back!
            let some gv := ctx.globals.get? key | throwError "unit {key} not in scope"
            let hl ← proveLookupG env gv.cname gv.value ctx.unfoldRec
            let hf ← mkAppOptM ``Eval_var #[env, shortIdent gv.cname, gv.value, mkApp gv.inv tupFn, hl, gv.cert]
            let (``Arrow, #[_, _, invT, _]) := gv.inv.getAppFnArgs | throwError "tupled unit invariant"
            let (_, gt) ← newEvalGoal env (mkApp invT tup)
            solve gt
            assignProof g (← mkAppM ``Eval_app_arrow #[hf, ← instantiateMVars (mkMVar gt)])
            return
  -- applications of global units: the key, then the data arguments
  if fn.isConst then
    if let some (key, dargs) ← splitKey t then
      if dargs.isEmpty then
        let some gv := ctx.globals.get? key | throwError "{key} has not been translated (or is not in scope)"
        let hl ← proveLookupG env gv.cname gv.value ctx.unfoldRec
        assignProof g (← mkAppOptM ``Eval_var #[env, shortIdent gv.cname, gv.value, mkApp gv.inv key, hl, gv.cert])
        return
      let fpart := mkAppN key dargs.pop
      let x := dargs.back!
      let invA ← invOf (← inferType x)
      let (_, gf) ← newEvalGoal env (mkApp (← mkAppM ``Arrow #[invA, inv]) fpart)
      let (_, gx) ← newEvalGoal env (mkApp invA x)
      solve gf; solve gx
      assignProof g (← mkAppM ``Eval_app_arrow #[← instantiateMVars (mkMVar gf), ← instantiateMVars (mkMVar gx)])
      return
  -- applications of local functions
  if fn.isFVar && args.size > 0 then
    let fpart := mkAppN fn args.pop
    let x := args.back!
    let invA ← invOf (← inferType x)
    let (_, gf) ← newEvalGoal env (mkApp (← mkAppM ``Arrow #[invA, inv]) fpart)
    let (_, gx) ← newEvalGoal env (mkApp invA x)
    solve gf; solve gx
    assignProof g (← mkAppM ``Eval_app_arrow #[← instantiateMVars (mkMVar gf), ← instantiateMVars (mkMVar gx)])
    return
  throwError "cannot translate {t}"

end

end ConPastel.Translator.Meta
