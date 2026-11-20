import ConPastel.Program.Command

/-! # Identity tokens (`cake_token`) with cached fields -/

namespace ConPastel.Examples.Token

inductive T where
  | leaf (n : Nat)
  | node (l r : T)
with
  @[computed_field] size : T → Nat
    | .leaf _ => 1
    | .node l r => l.size + r.size + 1

cake_cached T T.size
cake_token T

def build : List Nat → T
  | [] => .leaf 0
  | x :: xs => .node (.leaf x) (build xs)

def leftmost : T → Nat
  | .leaf n => n
  | .node l _ => leftmost l

/-- Accept inputs whose tree has a size ≡ 1 (mod 4), using the cached size,
the size of subtrees as a function value, and a pattern match. -/
def check (l : List Nat) : Bool :=
  let t := build l
  (t.size + ([t, .leaf 1].map T.size).length) % 4 == 3 && leftmost t == leftmost t

cake_unit check
cake_program tokenToy check

#print axioms tokenToy.correct

end ConPastel.Examples.Token
