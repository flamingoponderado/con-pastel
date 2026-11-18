import Lean
import ConPastel.Translator.Lemmas
import ConPastel.Translator.List
import ConPastel.Translator.Tuple
import ConPastel.Translator.Prims

/-!
# Equality types

`EqType A`: CakeML's structural equality (`doEq`) on representations decides
equality of the represented values. Then CakeML's `=` (`Eq` in the source,
`Equal_code` in the compiled program, which returns at once on identical
pointers) implements a decision of `x = y` (`Eval_eqType`).
-/

namespace ConPastel.Translator
open Classical
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- CakeML's `=` on representations decides equality of the values. -/
def EqType {α : Type} (A : RefInv α) : Prop :=
  ∀ x y v w, A x v → A y w → doEq v w = .val (decide (x = y))

theorem doEqList_nil : doEqList [] [] = .val true := by simp [doEqList]

theorem doEqList_cons {x y : Value} {xs ys : List Value} {b : Bool} (h : doEq x y = .val b) :
    doEqList (x :: xs) (y :: ys) = if b then doEqList xs ys else .val false := by
  cases b <;> simp [doEqList, h]

theorem doEq_conv_same {s : Option Stamp} {xs ys : List Value} (hl : xs.length = ys.length) :
    doEq (.conv s xs) (.conv s ys) = doEqList xs ys := by
  rw [doEq]; simp [hl]

theorem doEq_conv_diff {s t : Option Stamp} {xs ys : List Value} (hst : s ≠ t)
    (hsame : ctorSameType s t = true) :
    doEq (.conv s xs) (.conv t ys) = .val false := by
  rw [doEq]; simp [hst, hsame]

theorem eqType_NAT : EqType NAT := by
  intro x y v w hx hy; subst hx hy
  rw [doEq]; simp [litSameType, Int.ofNat_inj]

theorem eqType_UNIT : EqType UNIT := by
  intro x y v w hx hy; subst hx hy
  rw [doEq]; simp [doEqList]

theorem eqType_GHOST_unit : EqType (GHOST Unit) := by
  intro x y v w hx hy; subst hx hy
  rw [doEq]; simp [doEqList]

/-- A one-field structure is an equality type when its field is and the
projection is injective. -/
theorem eqType_NEWTYPE {S F : Type} {proj : S → F} {A : RefInv F} (hA : EqType A)
    (hinj : Function.Injective proj) : EqType (NEWTYPE proj A) := by
  intro x y v w hx hy
  rw [hA _ _ _ _ hx hy]
  congr 1
  exact decide_eq_decide.mpr ⟨fun h => hinj h, fun h => h ▸ rfl⟩

theorem eqType_PAIR {α β : Type} {A : RefInv α} {B : RefInv β} (hA : EqType A) (hB : EqType B) :
    EqType (PAIR A B) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ v w ⟨av, bv, ha, hb, rfl⟩ ⟨cv, dv, hc, hd, rfl⟩
  rw [doEq_conv_same (by simp), doEqList_cons (hA _ _ _ _ ha hc)]
  by_cases h1 : a = c
  · subst h1
    simp only [decide_true, ite_true]
    rw [doEqList_cons (hB _ _ _ _ hb hd)]
    by_cases h2 : b = d
    · subst h2; simp [doEqList]
    · simp [h2]
  · simp [h1]

theorem eqType_LIST {α : Type} {A : RefInv α} (hA : EqType A) : EqType (LIST A) := by
  intro x
  induction x with
  | nil =>
    intro y v w hx hy
    cases y with
    | nil => simp only [LIST] at hx hy; subst hx hy; rw [doEq_conv_same (by simp)]; simp [doEqList]
    | cons b bs =>
      simp only [LIST] at hx hy; obtain ⟨_, _, _, _, rfl⟩ := hy; subst hx
      rw [doEq_conv_diff (by simp [nilC, consC]; decide) (by simp [ctorSameType, sameType])]; simp
  | cons a as ih =>
    intro y v w hx hy
    cases y with
    | nil =>
      simp only [LIST] at hx hy; obtain ⟨_, _, _, _, rfl⟩ := hx; subst hy
      rw [doEq_conv_diff (by simp [nilC, consC]; decide) (by simp [ctorSameType, sameType])]; simp
    | cons b bs =>
      simp only [LIST] at hx hy
      obtain ⟨av, asv, ha, has, rfl⟩ := hx
      obtain ⟨bv, bsv, hb, hbs, rfl⟩ := hy
      rw [doEq_conv_same (by simp), doEqList_cons (hA _ _ _ _ ha hb)]
      by_cases h1 : a = b
      · subst h1
        simp only [decide_true, ite_true]
        rw [doEqList_cons (ih _ _ _ has hbs)]
        by_cases h2 : as = bs
        · subst h2; simp [doEqList]
        · simp [h2]
      · simp [h1]

/-- CakeML's `=` on representations of an equality type. -/
theorem Eval_eqType {α : Type} {A : RefInv α} (hA : EqType A) {env : SemEnv Value} {e₁ e₂ : Exp}
    {a b : α} (h₁ : Eval env e₁ (A a)) (h₂ : Eval env e₂ (A b)) :
    Eval env (.app .equality [e₁, e₂]) (BOOL (decide (a = b))) :=
  Eval_binop rfl h₁ h₂ fun v₁ v₂ p₁ p₂ => by
    refine ⟨_, rfl, fun refs ffi => ?_⟩
    simp [doApp, doAppBasic, doAppNumericCore, hA _ _ _ _ p₁ p₂]

theorem doEq_val_false_ctor {P : Prop} {inst : Decidable P} (h : ¬ P) :
    EqResult.val false = .val (@decide P inst) := by
  simp [h]

open Flapjack.Basis.Pure.MlString in
/-- The certificate of a primitive `f` compiled to CakeML's `=`
(`fn b => p = b`) at an equality type. -/
theorem primEq_cert {α : Type} {A : RefInv α} (hA : EqType A) {f : α → α → Bool}
    (hf : ∀ x y, f x y = true ↔ x = y)
    (envC : SemEnv Value) (funs : List (VarN × VarN × Exp)) (n : VarN)
    (hnodup : (funs.map fun (f, _, _) => f).Nodup)
    (hfind : findRecFun n funs = some (ofString "p", .fn (ofString "b") (.app .equality [V "p", V "b"]))) :
    Arrow A (Arrow A BOOL) f (.recclosure envC funs n) := by
  intro x xv hx
  apply AppReturns_recclosure hnodup hfind
  apply Eval_fn_arrow
  intro y yv hy
  have ha := Eval_var (SemEnv.mk (nsBind (ofString "b") yv (recBodyEnv envC funs (ofString "p") xv).v)
    (recBodyEnv envC funs (ofString "p") xv).c) _ xv _ (prim_lookup_p envC funs xv yv) hx
  have hb := Eval_var (SemEnv.mk (nsBind (ofString "b") yv (recBodyEnv envC funs (ofString "p") xv).v)
    (recBodyEnv envC funs (ofString "p") xv).c) _ yv _ (prim_lookup_b envC funs xv yv) hy
  refine Eval_weaken (Eval_eqType hA ha hb) fun w hw => ?_
  have : decide (x = y) = f x y := by
    by_cases e : x = y
    · simp [e, (hf y y).mpr rfl]
    · have : f x y = false := by
        cases h : f x y
        · rfl
        · exact absurd ((hf x y).mp h) e
      simp [e, this]
  rw [← this]; exact hw

/-! ## The tactic: `EqType N.cakeInv` for a generated datatype -/

section Tactic
open Lean Meta Elab Tactic

/-- `EqType A` for a field invariant: `NAT`, `LIST`, `PAIR`, one-field
structures (injective projection), `UNIT`, and datatypes already proved
(`cake_eqtype` lemmas passed as `extra`). -/
syntax "eqtype_field" ("[" term,* "]")? : tactic
macro_rules
  | `(tactic| eqtype_field $[[$ts,*]]?) => do
    let ts : Array (TSyntax `term) := match ts with | some ts => ts.getElems | none => #[]
    `(tactic| repeat' (first
        | exact eqType_NAT | exact eqType_UNIT
        $[| exact $ts]*
        | apply eqType_LIST | apply eqType_PAIR | apply eqType_NEWTYPE
        | (intro a b h; cases a; cases b; cases h; rfl)))

/-- Split every `∃`/`∧` hypothesis, then substitute the value equations. -/
partial def splitHyps (g : MVarId) : MetaM MVarId := do
  g.withContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``And 2 then
        let gs ← g.cases d.fvarId
        let [sg] := gs.toList | throwError "splitHyps: unexpected cases"
        return ← splitHyps sg.mvarId
    return g

elab "cake_split_hyps" : tactic => do
  let g ← getMainGoal
  let g ← splitHyps g
  replaceMainGoal [g]
  let v := mkIdent `v; let w := mkIdent `w
  evalTactic (← `(tactic| (subst $v:ident; subst $w:ident)))

/-- The hypothesis `A a x` about the value `x` (a local). -/
def findInvHyp (x : Expr) : MetaM (Expr × Expr × Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isApp && ty.appArg! == x && ty.appFn!.isApp then
      return (d.toExpr, ty.appFn!.appFn!, ty.appFn!.appArg!)
  throwError "eqtype: no invariant hypothesis for {x}"

/-- An induction hypothesis `∀ y v w, inv a v → inv y w → …` for `a`. -/
def findIH (inv a : Expr) : MetaM (Option Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let found ← forallTelescope ty fun xs _ => do
      if xs.size != 5 then return false
      let hty ← inferType xs[3]!
      return hty.isApp && hty.appFn!.isApp && hty.appFn!.appFn! == inv && hty.appFn!.appArg! == a
    if found then return some d.toExpr
  return none

/-- One constructor pair of `EqType N.cakeInv`, after splitting. -/
partial def eqTypeCase (inv : Expr) (extra : Array (TSyntax `term)) : TacticM Unit := do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := ty.eq? | throwError "eqtype: not an equation {ty}"
  if lhs.isAppOfArity ``doEq 2 then
    let v := lhs.appFn!.appArg!; let w := lhs.appArg!
    let (.app (.app (.const ``Value.conv _) s) _) := v | throwError "eqtype: {v}"
    let (.app (.app (.const ``Value.conv _) t) _) := w | throwError "eqtype: {w}"
    if s != t then
      evalTactic (← `(tactic| rw [doEq_conv_diff (by simp <;> decide) (by simp [ctorSameType, sameType])]))
      evalTactic (← `(tactic| refine doEq_val_false_ctor ?_))
      evalTactic (← `(tactic| (intro e; cases e)))
      return
    evalTactic (← `(tactic| rw [doEq_conv_same (by simp)]))
    return ← eqTypeCase inv extra
  if lhs.isAppOfArity ``doEqList 2 then
    let xs := lhs.appFn!.appArg!; let ys := lhs.appArg!
    if xs.isAppOfArity ``List.nil 1 then
      evalTactic (← `(tactic| simp [doEqList]))
      return
    let x := xs.appFn!.appArg!; let y := ys.appFn!.appArg!
    let fact ← g.withContext do
      let (hx, A, a) ← findInvHyp x
      let (hy, _, b) ← findInvHyp y
      if let some ih ← findIH A a then
        pure (mkAppN ih #[b, x, y, hx, hy])
      else
        let m ← mkFreshExprMVar (← mkAppM ``EqType #[A])
        let rest ← Tactic.run m.mvarId! (evalTactic (← `(tactic| eqtype_field [$extra,*])))
        unless rest.isEmpty do throwError "eqtype: no equality-type proof for {A}"
        pure (mkAppN (← instantiateMVars m) #[a, b, x, y, hx, hy])
    let r ← g.withContext do g.rewrite (← g.getType) (← mkAppOptM ``doEqList_cons #[none, none, xs.appArg!, ys.appArg!, none, fact])
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (g' :: r.mvarIds)
    let some (_, _, rhs0) := (← instantiateMVars (← inferType fact)).eq? | throwError "eqtype: fact"
    let p := rhs0.appArg!.appArg!  -- `decide (a = b)` → `a = b`
    let cond := p.appArg!
    let _ := cond
    let hc := mkIdent `hc
    evalTactic (← `(tactic| by_cases $hc:ident : $(← Term.exprToSyntax p.appArg!)))
    -- negative branch first in the goal list? `by_cases` gives [pos, neg]
    let gs ← getGoals
    match gs with
    | pos :: neg :: rest =>
      setGoals [neg]
      let (lhsP, rhsP) := (p.appArg!.appFn!.appArg!, p.appArg!.appArg!)
      if lhsP == rhsP then
        evalTactic (← `(tactic| exact absurd rfl $hc:ident))
      else
        evalTactic (← `(tactic| simp only [$hc:ident, decide_false, Bool.false_eq_true, ite_false]))
        evalTactic (← `(tactic| refine doEq_val_false_ctor ?_))
        evalTactic (← `(tactic| (intro e; apply $hc:ident; cases e; rfl)))
      setGoals [pos]
      evalTactic (← `(tactic| first | (subst $hc:ident; simp only [decide_true, ite_true]) | simp only [$hc:ident, decide_true, ite_true]))
      eqTypeCase inv extra
      setGoals ((← getGoals) ++ rest)
    | _ => throwError "eqtype: by_cases"
    return
  throwError "eqtype: unexpected goal {ty}"

syntax "cake_eqtype_step" ident ("[" term,* "]")? : tactic
elab_rules : tactic
  | `(tactic| cake_eqtype_step $i:ident $[[$ts,*]]?) => do
    let extra : Array (TSyntax `term) := match ts with | some ts => ts.getElems | none => #[]
    let inv ← realizeGlobalConstNoOverloadWithInfo i
    eqTypeCase (mkConst inv) extra

/-- `cake_eqtype [lemmas]`: prove `EqType N.cakeInv` for a generated
datatype `N` (structural recursion), with the equality-type lemmas of the
datatypes its fields use. -/
syntax "cake_eqtype" ("[" term,* "]")? : tactic
elab_rules : tactic
  | `(tactic| cake_eqtype $[[$ts,*]]?) => do
    let extra : Array (TSyntax `term) := match ts with | some ts => ts.getElems | none => #[]
    let g ← getMainGoal
    let ty ← whnfR (← instantiateMVars (← g.getType))
    let .app _ inv := ty | throwError "cake_eqtype: goal is not `EqType inv`"
    let .const invName _ := inv | throwError "cake_eqtype: {inv} is not a constant"
    let invId := mkIdent invName
    evalTactic (← `(tactic| (unfold EqType; intro x; induction x)))
    let gs ← getGoals
    for c in gs do
      setGoals [c]
      let (y, v, w, hx, hy) := (mkIdent `y, mkIdent `v, mkIdent `w, mkIdent `hx, mkIdent `hy)
      evalTactic (← `(tactic| intro $y:ident $v:ident $w:ident $hx:ident $hy:ident))
      evalTactic (← `(tactic| cases $y:ident <;> simp only [$invId:ident] at $hx:ident $hy:ident))
      for c' in ← getGoals do
        setGoals [c']
        evalTactic (← `(tactic| cake_split_hyps))
        eqTypeCase inv extra
    setGoals []

end Tactic

end ConPastel.Translator
