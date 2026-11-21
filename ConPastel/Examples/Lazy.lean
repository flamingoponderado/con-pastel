import ConPastel.Program.Command

/-! # Lazy fields (`cake_lazy`): fields stored as closures, computed when read -/

namespace ConPastel.Examples.Lazy

structure S where
  name : Nat
  big : List Nat
  other : List Nat

cake_lazy S big other
cake_datatype S

def bigList : List Nat := (List.range 50).map (· * 3)

def table : List S := [⟨1, bigList, [2]⟩, ⟨2, [], bigList⟩]

def pick (n : Nat) : List Nat :=
  match table.find? (·.name == n) with
  | some s => s.big ++ s.other
  | none => []

/-- Accept inputs of length ≡ length of `pick 1` (mod 7), reading lazy fields
by projection and by pattern match. -/
def check (l : List Nat) : Bool :=
  let s : S := ⟨l.length, l, []⟩
  (pick 1).length % 7 == l.length % 7 && (match s with | ⟨_, b, o⟩ => b.length + o.length) == s.name

cake_unit check
cake_program lazyToy check

#print axioms lazyToy.correct

end ConPastel.Examples.Lazy
