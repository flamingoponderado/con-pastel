import ConPastel.Program.Command

/-! # A toy end-to-end program: accept inputs of even length -/

namespace ConPastel.Examples.Toy

def evenLen : List Nat → Bool
  | [] => true
  | [_] => false
  | _ :: _ :: xs => evenLen xs

cake_unit evenLen

cake_program toy evenLen

#check @toy.correct
#print axioms toy.correct

end ConPastel.Examples.Toy
