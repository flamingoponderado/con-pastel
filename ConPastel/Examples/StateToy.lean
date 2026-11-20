import ConPastel.Program.Command
import ConPastel.Translator.Replace

/-! # A state-exception computation translated over a reference -/

namespace ConPastel.Examples.StateToy

cake_state_ref Nat

def bumpBy (k : Nat) : StateT Nat (Except Nat) Unit := modify (· + k)

def prog (k : Nat) : StateT Nat (Except Nat) Nat := do
  bumpBy k
  bumpBy 1
  let x ← get
  if x > 100 then throw x else pure (x * 2)

cake_unit bumpBy
cake_unit prog

/-- Run `prog` from each start in the list (each run on a fresh reference). -/
def runAll (l : List Nat) : Bool :=
  l.all fun k => match ConPastel.Translator.runRef k (prog k) with
    | .ok v => v % 2 == 0
    | .error e => e > 100

cake_unit runAll
cake_program stateToy runAll
#print axioms stateToy.correct

end ConPastel.Examples.StateToy
