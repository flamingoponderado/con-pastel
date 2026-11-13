import ConPastel.Translator.Datatype

/-!
# The CakeML prelude: primitives whose CakeML behaviour differs from Lean's

`Nat` subtraction truncates at 0, and `Nat` division and modulo by 0 return
0 and the dividend, while CakeML's integer operations go negative or raise
`Div`. Each prelude function is a closed CakeML closure with a certificate
against the Lean function.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString

/-- A variable expression. -/
def V (s : String) : Exp := .var (.short (ofString s))

/-- Lookup of a variable bound by the innermost two closures. -/
theorem lookup_fn2_inner (env : SemEnv Value) (a b : VarN) (av bv : Value) :
    nsLookup (nsBind b bv (nsBind a av env.v)) (.short b) = some bv := by
  simp [nsLookup_nsBind_short]

theorem lookup_fn2_outer (env : SemEnv Value) (a b : VarN) (av bv : Value) (h : a ≠ b) :
    nsLookup (nsBind b bv (nsBind a av env.v)) (.short a) = some av := by
  simp [nsLookup_nsBind_short, h]

/-- A curried two-argument closure: `fn a => fn b => body`. -/
theorem Eval_fn2 {α β γ : Type} {A : RefInv α} {B : RefInv β} {C : RefInv γ}
    {env : SemEnv Value} {a b : VarN} {body : Exp} {f : α → β → γ}
    (h : ∀ x xv y yv, A x xv → B y yv →
      Eval { v := nsBind b yv (nsBind a xv env.v), c := env.c } body (C (f x y))) :
    Eval env (.fn a (.fn b body)) (Arrow A (Arrow B C) f) := by
  apply Eval_fn_arrow
  intro x xv hx
  apply Eval_fn_arrow
  intro y yv hy
  exact h x xv y yv hx hy

/-! ## Nat subtraction -/

/-- `fn a => fn b => if a < b then 0 else a - b` -/
def natSubExp : Exp :=
  .fn (ofString "a") (.fn (ofString "b")
    (.if_ (.app (.test (.compare .lt) .intT) [V "a", V "b"]) (.lit (.intLit 0))
      (.app (.arith .sub .intT) [V "a", V "b"])))

theorem natSub_cert (env : SemEnv Value) : Eval env natSubExp (Arrow NAT (Arrow NAT NAT) Nat.sub) := by
  apply Eval_fn2
  intro x xv y yv hx hy
  let E : SemEnv Value := { v := nsBind (ofString "b") yv (nsBind (ofString "a") xv env.v), c := env.c }
  have ha : Eval E (V "a") (INT x) :=
    Eval_var E _ xv _ (lookup_fn2_outer env (ofString "a") (ofString "b") xv yv (by decide)) hx
  have hb : Eval E (V "b") (INT y) :=
    Eval_var E _ yv _ (lookup_fn2_inner env (ofString "a") (ofString "b") xv yv) hy
  refine Eval_if (Eval_int_cmp .lt ha hb) (fun h => ?_) (fun h => ?_)
  · exact Eval_lit _ _ _ (by
      have : (x : Int) < y := by simpa [(intCmp_spec _ _).1] using h
      simp [NAT]; omega)
  · exact Eval_weaken (Eval_int_sub ha hb) fun w hw => by
      have : ¬ (x : Int) < y := by simpa [(intCmp_spec _ _).1] using h
      simp only [INT] at hw; simp only [NAT, hw, Nat.sub_eq]; congr 2; omega

end ConPastel.Translator
