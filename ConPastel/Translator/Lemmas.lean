import ConPastel.Translator.Prelude
import ConPastel.Semantics.Init

/-!
# Lemmas in the shape the translator emits

Each lemma relates a CakeML construct to the Lean construct it translates,
with invariants applied to Lean terms, so the translator can chain them by
unification.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- Decidable propositions are represented by their truth value. -/
def DEC (p : Prop) [Decidable p] (v : Value) : Prop := BOOL (decide p) v

theorem Eval_ite {α : Type} {A : RefInv α} {env : SemEnv Value} {c : Prop} [Decidable c]
    {ec e₁ e₂ : Exp} {t e : α} (hc : Eval env ec (BOOL (decide c)))
    (h₁ : c → Eval env e₁ (A t)) (h₂ : ¬c → Eval env e₂ (A e)) :
    Eval env (.if_ ec e₁ e₂) (A (if c then t else e)) :=
  Eval_if hc (fun h => by have hc' : c := of_decide_eq_true h; simpa [hc'] using h₁ hc')
    (fun h => by have hc' : ¬c := of_decide_eq_false h; simpa [hc'] using h₂ hc')

theorem Eval_dite {α : Type} {A : RefInv α} {env : SemEnv Value} {c : Prop} [Decidable c]
    {ec e₁ e₂ : Exp} {t : c → α} {e : ¬c → α} (hc : Eval env ec (BOOL (decide c)))
    (h₁ : ∀ h : c, Eval env e₁ (A (t h))) (h₂ : ∀ h : ¬c, Eval env e₂ (A (e h))) :
    Eval env (.if_ ec e₁ e₂) (A (if h : c then t h else e h)) :=
  Eval_if hc (fun h => by have hc' : c := of_decide_eq_true h; simpa [hc'] using h₁ hc')
    (fun h => by have hc' : ¬c := of_decide_eq_false h; simpa [hc'] using h₂ hc')

/-! ## Nat as integers -/

theorem NAT_iff_INT (n : Nat) (v : Value) : NAT n v ↔ INT (n : Int) v := Iff.rfl

theorem Eval_nat_lit (env : SemEnv Value) (n : Nat) :
    Eval env (.lit (.intLit n)) (NAT n) := Eval_lit _ _ _ rfl

theorem Eval_nat_add {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Nat}
    (h₁ : Eval env e₁ (NAT a)) (h₂ : Eval env e₂ (NAT b)) :
    Eval env (.app (.arith .add .intT) [e₁, e₂]) (NAT (a + b)) :=
  Eval_weaken (Eval_int_add h₁ h₂) fun v hv => by simpa [NAT, INT] using hv

theorem Eval_nat_mul {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Nat}
    (h₁ : Eval env e₁ (NAT a)) (h₂ : Eval env e₂ (NAT b)) :
    Eval env (.app (.arith .mul .intT) [e₁, e₂]) (NAT (a * b)) :=
  Eval_weaken (Eval_int_mul h₁ h₂) fun v hv => by simpa [NAT, INT] using hv

theorem Eval_nat_lt {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Nat}
    (h₁ : Eval env e₁ (NAT a)) (h₂ : Eval env e₂ (NAT b)) :
    Eval env (.app (.test (.compare .lt) .intT) [e₁, e₂]) (BOOL (decide (a < b))) :=
  Eval_weaken (Eval_int_cmp .lt h₁ h₂) fun v hv => by
    simpa [(intCmp_spec _ _).1] using hv

theorem Eval_nat_le {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Nat}
    (h₁ : Eval env e₁ (NAT a)) (h₂ : Eval env e₂ (NAT b)) :
    Eval env (.app (.test (.compare .leq) .intT) [e₁, e₂]) (BOOL (decide (a ≤ b))) :=
  Eval_weaken (Eval_int_cmp .leq h₁ h₂) fun v hv => by
    simpa [(intCmp_spec _ _).2.1] using hv

theorem Eval_nat_eq {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Nat}
    (h₁ : Eval env e₁ (NAT a)) (h₂ : Eval env e₂ (NAT b)) :
    Eval env (.app .equality [e₁, e₂]) (BOOL (decide (a = b))) :=
  Eval_weaken (Eval_int_eq h₁ h₂) fun v hv => by simpa [Int.natCast_inj] using hv

/-- `Nat.sub` through the prelude closure bound at `natSubName`. -/
theorem Eval_nat_sub {env : SemEnv Value} {fe e₁ e₂ : Exp} {a b : Nat}
    (hf : Eval env fe (Arrow NAT (Arrow NAT NAT) Nat.sub))
    (h₁ : Eval env e₁ (NAT a)) (h₂ : Eval env e₂ (NAT b)) :
    Eval env (.app .opapp [.app .opapp [fe, e₁], e₂]) (NAT (a - b)) :=
  Eval_app_arrow (Eval_app_arrow hf h₁) h₂

/-! ## Booleans -/

/-- The constructor environment has CakeML's boolean constructors. -/
structure HasBoolCons (envC : Namespace ModN ConN (Nat × Stamp)) : Prop where
  true_ : nsLookup envC (.short (Basis.Pure.MlString.ofString "True")) =
    some (0, .typeStamp (Basis.Pure.MlString.ofString "True") 0)
  false_ : nsLookup envC (.short (Basis.Pure.MlString.ofString "False")) =
    some (0, .typeStamp (Basis.Pure.MlString.ofString "False") 0)

theorem initEnv_hasBoolCons : HasBoolCons ConPastel.initEnv.c := ⟨by decide, by decide⟩

/-- The CakeML expression for a boolean literal. -/
def boolLit (b : Bool) : Exp :=
  .con (some (.short (Basis.Pure.MlString.ofString (if b then "True" else "False")))) []

theorem Eval_bool_lit {env : SemEnv Value} (h : HasBoolCons env.c) (b : Bool) :
    Eval env (boolLit b) (BOOL b) := by
  have hl : nsLookup env.c (.short (Basis.Pure.MlString.ofString (if b then "True" else "False"))) =
      some (([] : List Exp).length,
        .typeStamp (Basis.Pure.MlString.ofString (if b then "True" else "False")) 0) := by
    cases b
    · exact h.false_
    · exact h.true_
  refine Eval_weaken (Eval_con (Ps := []) hl trivial) fun v ⟨vs, hvs, hv⟩ => ?_
  cases hvs
  subst hv
  cases b <;> rfl

end ConPastel.Translator
