import ConPastel.Program.Command

/-! # A mutually recursive (well-founded) block, end to end -/

namespace ConPastel.Examples.Mutual

mutual
def ev : Nat → List Nat → Bool
  | 0, _ => true
  | n+1, l => od n (n :: l)
termination_by n => n
def od : Nat → List Nat → Bool
  | 0, _ => false
  | n+1, l => ev n l
termination_by n => n
end

def evenLen (l : List Nat) : Bool := ev l.length []

cake_unit evenLen
cake_program mutp evenLen
#print axioms mutp.correct

end ConPastel.Examples.Mutual
