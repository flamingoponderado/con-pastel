import ConPastel.Program.Command
import ConPastel.Translator.EqSound

/-! # Identity tokens (`cake_token`) with cached fields, and the pointer test -/

namespace ConPastel.Examples.Token
open ConPastel.Translator

inductive T where
  | leaf (n : Nat)
  | node (l r : T)
with
  @[computed_field] size : T → Nat
    | .leaf _ => 1
    | .node l r => l.size + r.size + 1

cake_cached T T.size
cake_token T
cake_datatype T

theorem eqSound_T : EqSound ConPastel.CakeT.t2.cakeInv := by cake_eqsound
cake_eqsound_reg eqSound_T

def build : List Nat → T
  | [] => .leaf 0
  | x :: xs => .node (.leaf x) (build xs)

def leftmost : T → Nat
  | .leaf n => n
  | .node l _ => leftmost l

/-- Structural equality. -/
def eqT : T → T → Bool
  | .leaf a, .leaf b => a == b
  | .node a b, .node c d => eqT a c && eqT b d
  | _, _ => false

theorem eqT_refl : ∀ t, eqT t t = true
  | .leaf _ => by simp [eqT]
  | .node a b => by simp [eqT, eqT_refl a, eqT_refl b]

/-- Equality with a pointer test first. -/
def same (t u : T) : Bool :=
  ptrSel t u (fun _ => true) (eqT t u) (by intro p; subst p; simp [eqT_refl])

/-- Accept inputs whose tree has a size ≡ 1 (mod 4), using the cached size,
the size of subtrees as a function value, a pattern match, and the pointer
test (on the same object, and on equal objects built separately). -/
def check (l : List Nat) : Bool :=
  let t := build l
  (t.size + ([t, .leaf 1].map T.size).length) % 4 == 3 && leftmost t == leftmost t &&
    same t t && same t (build l) && !same t (.leaf 7)

cake_unit check
cake_program tokenToy check

#print axioms tokenToy.correct

end ConPastel.Examples.Token
