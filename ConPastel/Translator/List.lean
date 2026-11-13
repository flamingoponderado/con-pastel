import ConPastel.Translator.Datatype
import ConPastel.Semantics.Init

/-! # The list invariant -/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString

def nilC : ConN := ofString "[]"
def consC : ConN := ofString "::"

/-- CakeML's built-in lists (type stamp 1). -/
def LIST {α : Type} (a : RefInv α) : RefInv (List α)
  | [], v => v = .conv (some (.typeStamp nilC 1)) []
  | x :: xs, v => ∃ xv xsv, a x xv ∧ LIST a xs xsv ∧ v = .conv (some (.typeStamp consC 1)) [xv, xsv]

/-- The constructor environment has CakeML's list constructors. -/
structure HasListCons (envC : Namespace ModN ConN (Nat × Stamp)) : Prop where
  nil : nsLookup envC (.short nilC) = some (0, .typeStamp nilC 1)
  cons : nsLookup envC (.short consC) = some (2, .typeStamp consC 1)

theorem initEnv_hasListCons : HasListCons ConPastel.initEnv.c := ⟨by decide, by decide⟩

/-- A flat match over lists. -/
theorem listCases_flat {envC : Namespace ModN ConN (Nat × Stamp)} (h : HasListCons envC)
    (bn : Exp) (x xs : VarN) (bc : Exp) (hx : x ≠ xs) :
    FlatCases envC 1 [(nilC, [], bn), (consC, [x, xs], bc)] where
  lookup c ys b hm := by
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact h.nil
    · exact h.cons
  nodupC := by simp only [List.map_cons, List.map_nil]; decide
  nodupX c ys b hm := by
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp
    · simp [hx]

theorem Eval_nil {α : Type} {A : RefInv α} {env : SemEnv Value} (hc : HasListCons env.c) :
    Eval env (.con (some (.short nilC)) []) (LIST A []) := by
  refine Eval_weaken (Eval_con (Ps := []) (by simpa using hc.nil) trivial) ?_
  rintro v ⟨vs, hvs, rfl⟩
  cases hvs
  rfl

theorem Eval_cons {α : Type} {A : RefInv α} {env : SemEnv Value} (hc : HasListCons env.c)
    {e₁ e₂ : Exp} {x : α} {xs : List α} (h₁ : Eval env e₁ (A x)) (h₂ : Eval env e₂ (LIST A xs)) :
    Eval env (.con (some (.short consC)) [e₁, e₂]) (LIST A (x :: xs)) := by
  refine Eval_weaken (Eval_con (Ps := [LIST A xs, A x]) (by simpa using hc.cons) ⟨h₂, h₁, trivial⟩) ?_
  rintro v ⟨vs, hvs, rfl⟩
  match vs, hvs with
  | [w₁, w₀], .cons hw₁ (.cons hw₀ .nil) => exact ⟨w₀, w₁, hw₀, hw₁, rfl⟩

theorem list_cake_mat {α : Type} {A : RefInv α} {env : SemEnv Value} (hc : HasListCons env.c)
    {e : Exp} {xs : List α} (he : Eval env e (LIST A xs)) {Q : List α → Value → Prop}
    (bn : Exp) (hn : xs = [] → Eval (clauseEnv env [] []) bn (Q []))
    (nx ny : VarN) (hne : nx ≠ ny) (bc : Exp)
    (hcons : ∀ a as, xs = a :: as → ∀ w₀ w₁, A a w₀ → LIST A as w₁ →
      Eval (clauseEnv env [nx, ny] [w₀, w₁]) bc (Q (a :: as))) :
    Eval env (.mat e (conClauses [(nilC, [], bn), (consC, [nx, ny], bc)])) (Q xs) := by
  refine Eval_mat (listCases_flat hc bn nx ny bc hne) he ?_
  intro v hv
  cases xs with
  | nil => exact ⟨nilC, [], bn, [], by simp, hv, rfl, hn rfl⟩
  | cons a as =>
    obtain ⟨w₀, w₁, h₀, h₁, rfl⟩ := hv
    exact ⟨consC, [nx, ny], bc, [w₀, w₁], by simp, rfl, rfl, hcons a as rfl w₀ w₁ h₀ h₁⟩

end ConPastel.Translator
