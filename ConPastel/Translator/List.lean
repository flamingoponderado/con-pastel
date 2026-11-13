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

end ConPastel.Translator
