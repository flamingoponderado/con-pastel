import ConPastel.Program.Command
import ConPastel.Translator.Replace

/-! # A computation over a CakeML `Array.array`, updated in place -/

namespace ConPastel.Examples.ArrayStateToy
open ConPastel.Translator

cake_state_array Nat

def bump (i : Nat) : StateT (Array Nat) (Except Nat) Unit := do
  let v ← getsD i 0
  setM i (v + 1)

def countAll : List Nat → StateT (Array Nat) (Except Nat) Unit
  | [] => pure ()
  | x :: xs => do bump (x % 8); countAll xs

/-- Count into 8 buckets, in place, and check bucket 3. -/
def histo (l : List Nat) : Bool :=
  match runArr 8 0 (do countAll l; getsD 3 0) with
  | .ok c => c == l.countP (· % 8 == 3)
  | .error _ => false

cake_unit histo
cake_program arrToy histo
#print axioms arrToy.correct

end ConPastel.Examples.ArrayStateToy
