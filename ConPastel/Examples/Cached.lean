import ConPastel.Program.Command

/-! # Cached computed fields (`cake_cached`) -/

namespace ConPastel.Examples.Cached

inductive T where
  | leaf (n : Nat)
  | node (l r : T)
with
  @[computed_field] size : T → Nat
    | .leaf _ => 1
    | .node l r => l.size + r.size + 1

cake_cached T T.size

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
cake_program cached check

#print axioms cached.correct

end ConPastel.Examples.Cached
#print axioms ConPastel.CakeT.t2.cake_cf0
#print axioms ConPastel.CakeT.t2.cake_mat
#print axioms ConPastel.CakeT.t2.con0
#print axioms ConPastel.CakeT.t2.con1
