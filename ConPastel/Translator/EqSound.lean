import ConPastel.Translator.EqType
import ConPastel.Translator.Token

/-!
# Sound equality types

On a datatype with identity tokens (`cake_token`) CakeML's `=` no longer
decides equality, but it never fails, and `true` means equal values:
`EqSound A`. That is what a *pointer test* needs (`Eval_ptrSel`).
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

theorem eqOut_of_eqType {α : Type} {A : RefInv α} (hA : EqType A) {a b : α} {v w : Value}
    (ha : A a v) (hb : A b w) : EqOut (doEq v w) (a = b) := by
  rw [hA _ _ _ _ ha hb]
  by_cases h : a = b
  · exact .inr ⟨by simp [h], h⟩
  · exact .inl (by simp [h])

theorem eqSound_of_eqType {α : Type} {A : RefInv α} (hA : EqType A) : EqSound A :=
  fun _ _ _ _ ha hb => eqOut_of_eqType hA ha hb

end ConPastel.Translator

/-! ## The tactic: `EqSound N.cakeInv` for a generated datatype with tokens -/

namespace ConPastel.Translator
section Tactic
open Lean Meta Elab Tactic
open Flapjack.SemanticPrimitivesHOL

/-- The hypothesis `TOKEN x`, if any. -/
def findTokHyp (x : Expr) : MetaM (Option Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``TOKEN 1 && ty.appArg! == x then return some d.toExpr
  return none

/-- One constructor pair of `EqSound N.cakeInv`, after splitting. -/
partial def eqSoundCase (extra : Array (TSyntax `term)) : TacticM Unit := do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``EqOut 2 do throwError "eqsound: unexpected goal {ty}"
  let r := ty.appFn!.appArg!
  if r.isAppOfArity ``doEq 2 then
    let v := r.appFn!.appArg!; let w := r.appArg!
    let (.app (.app (.const ``Value.conv _) s) _) := v | throwError "eqsound: {v}"
    let (.app (.app (.const ``Value.conv _) t) _) := w | throwError "eqsound: {w}"
    if s != t then
      evalTactic (← `(tactic| exact eqOut_false (doEq_conv_diff (by simp <;> decide) (by simp [ctorSameType, sameType]))))
      return
    evalTactic (← `(tactic| rw [doEq_conv_same (by simp)]))
    return ← eqSoundCase extra
  if r.isAppOfArity ``doEqList 2 then
    let xs := r.appFn!.appArg!; let ys := r.appArg!
    if xs.isAppOfArity ``List.nil 1 then
      evalTactic (← `(tactic| exact eqOut_nil rfl))
      return
    let x := xs.appFn!.appArg!; let y := ys.appFn!.appArg!
    let fact ← g.withContext do
      if let some hx ← findTokHyp x then
        let some hy ← findTokHyp y | throwError "eqsound: no token hypothesis for {y}"
        return ← mkAppM ``eqOut_token #[hx, hy]
      let (hx, A, a) ← findInvHyp x
      let (hy, _, b) ← findInvHyp y
      if let some ih ← findIH A a then
        return mkAppN ih #[b, x, y, hx, hy]
      let m ← mkFreshExprMVar (← mkAppM ``EqType #[A])
      let rest ← Tactic.run m.mvarId! (evalTactic (← `(tactic| eqtype_field [$extra,*])))
      unless rest.isEmpty do throwError "eqsound: no equality-type proof for {A}"
      mkAppM ``eqOut_of_eqType #[← instantiateMVars m, hx, hy]
    let fs ← g.withContext (Term.exprToSyntax fact)
    let hp := mkIdent `hp
    evalTactic (← `(tactic| refine eqOut_cons $fs fun $hp:ident => ?_))
    evalTactic (← `(tactic| try subst $hp:ident))
    return ← eqSoundCase extra
  throwError "eqsound: unexpected goal {ty}"

/-- `cake_eqsound [lemmas]`: prove `EqSound N.cakeInv` for a generated datatype
`N` with identity tokens (structural recursion), with the equality-type lemmas
of the datatypes its fields use. -/
syntax "cake_eqsound" ("[" term,* "]")? : tactic
elab_rules : tactic
  | `(tactic| cake_eqsound $[[$ts,*]]?) => do
    let extra : Array (TSyntax `term) := match ts with | some ts => ts.getElems | none => #[]
    let g ← getMainGoal
    let ty ← whnfR (← instantiateMVars (← g.getType))
    let .app _ inv := ty | throwError "cake_eqsound: goal is not `EqSound inv`"
    let .const invName _ := inv | throwError "cake_eqsound: {inv} is not a constant"
    let invId := mkIdent invName
    evalTactic (← `(tactic| (unfold EqSound; intro x; induction x)))
    let gs ← getGoals
    for c in gs do
      setGoals [c]
      let (y, v, w, hx, hy) := (mkIdent `y, mkIdent `v, mkIdent `w, mkIdent `hx, mkIdent `hy)
      evalTactic (← `(tactic| intro $y:ident $v:ident $w:ident $hx:ident $hy:ident))
      evalTactic (← `(tactic| cases $y:ident <;> simp only [$invId:ident] at $hx:ident $hy:ident))
      for c' in ← getGoals do
        setGoals [c']
        evalTactic (← `(tactic| cake_split_hyps))
        eqSoundCase extra
    setGoals []

end Tactic
end ConPastel.Translator
