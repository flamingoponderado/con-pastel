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

namespace ConPastel.Examples.Toy

/-- The toy reference checker on byte arrays. -/
def toyRef (input : ByteArray) : Bool := evenLen (input.toList.map UInt8.toNat)

theorem toy_implements : ConPastel.ImplementsRef toyRef toy.prog :=
  ConPastel.implementsRef_of_completes toyRef toy.prog toy.correct

#print axioms toy_implements

end ConPastel.Examples.Toy
