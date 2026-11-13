import ConPastel.Program.Command
import ConPastel.Translator.Meta.Datatype

/-! # A toy end-to-end program with a datatype -/

namespace ConPastel.Examples.Toy2

inductive Mode where
  | even
  | odd

cake_datatype Mode

def flip : Mode → Mode
  | .even => .odd
  | .odd => .even

def modeOf : List Nat → Mode
  | [] => .even
  | _ :: xs => flip (modeOf xs)

def isEven : Mode → Bool
  | .even => true
  | .odd => false

def entry2 (xs : List Nat) : Bool := isEven (modeOf xs)

cake_unit flip modeOf isEven entry2

cake_program toy2 entry2

theorem toy2_implements (h : ConPastel.RuntimeAssumptions) :
    ConPastel.ImplementsRef (fun input => entry2 (input.toList.map UInt8.toNat)) toy2.prog :=
  ConPastel.implementsRef_of_completes _ _ (toy2.correct h)

#print axioms toy2_implements

end ConPastel.Examples.Toy2
