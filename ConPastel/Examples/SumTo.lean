import ConPastel.Translator.Recursion

/-!
# Milestone 2 check: a hand-applied certificate for a recursive function

`sumTo n = if n = 0 then 0 else n + sumTo (n - 1)` on `Nat`, translated to
the CakeML recursive closure `sumToClosure`, proved by functional induction.
-/

namespace ConPastel.Examples
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString ConPastel.Translator

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

def sumToBody : Exp :=
  .if_ (.app .equality [.var (.short (ofString "n")), .lit (.intLit 0)])
    (.lit (.intLit 0))
    (.app (.arith .add .intT)
      [.var (.short (ofString "n")),
       .app .opapp [.var (.short (ofString "sumTo")),
         .app (.arith .sub .intT) [.var (.short (ofString "n")), .lit (.intLit 1)]]])

def sumToFuns : List (VarN × VarN × Exp) := [(ofString "sumTo", ofString "n", sumToBody)]

def sumToClosure (envC : SemEnv Value) : Value := .recclosure envC sumToFuns (ofString "sumTo")

theorem lookup_n (envC : SemEnv Value) (xv : Value) :
    nsLookup (recBodyEnv envC sumToFuns (ofString "n") xv).v (.short (ofString "n")) = some xv := by
  simp [recBodyEnv, nsLookup_nsBind_short]

theorem lookup_sumTo (envC : SemEnv Value) (xv : Value) :
    nsLookup (recBodyEnv envC sumToFuns (ofString "n") xv).v (.short (ofString "sumTo")) =
      some (sumToClosure envC) := by
  have hne : ofString "sumTo" ≠ ofString "n" := by decide
  simp only [recBodyEnv, nsLookup_nsBind_short, hne, ite_false]
  exact nsLookup_buildRecEnv (by decide)

theorem sumTo_cert (envC : SemEnv Value) : Arrow NAT NAT sumTo (sumToClosure envC) := by
  intro x
  induction x with
  | zero =>
    intro xv hx
    apply AppReturns_recclosure (x := ofString "n") (body := sumToBody) (by decide)
      (by simp [findRecFun, sumToFuns])
    unfold sumToBody
    refine Eval_if (Eval_int_eq (Eval_var _ _ xv _ (lookup_n envC xv) hx) (Eval_lit _ _ (INT 0) rfl))
      (fun _ => Eval_lit _ _ _ rfl) (fun h => by simp at h)
  | succ m ih =>
    intro xv hx
    apply AppReturns_recclosure (x := ofString "n") (body := sumToBody) (by decide)
      (by simp [findRecFun, sumToFuns])
    unfold sumToBody
    have hn : Eval (recBodyEnv envC sumToFuns (ofString "n") xv) (.var (.short (ofString "n")))
        (INT ((m + 1 : Nat) : Int)) := Eval_var _ _ xv _ (lookup_n envC xv) hx
    refine Eval_if (Eval_int_eq hn (Eval_lit _ _ (INT 0) rfl)) (fun h => by simp at h; omega) ?_
    intro _
    have hrec := Eval_app (Eval_var _ _ _ (fun v => v = sumToClosure envC) (lookup_sumTo envC xv) rfl)
      (Eval_int_sub hn (Eval_lit _ _ (INT 1) rfl)) (Q := INT (sumTo m))
      (fun fv yv hf hy => by
        subst hf
        exact ih yv (by simp only [INT] at hy; simp [NAT, hy]))
    exact Eval_weaken (Eval_int_add hn hrec) (fun v hv => by
      simp only [INT] at hv; simp [NAT, sumTo, hv])

end ConPastel.Examples
