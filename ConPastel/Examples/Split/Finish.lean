import ConPastel.Examples.Split.Part0
import ConPastel.Examples.Split.Part1

namespace ConPastel.Examples.Split

cake_mutual_finish a

def top (l : List Nat) : Bool := a l.length [] == 7

cake_unit top
cake_program splitProg top
#print axioms splitProg.correct

end ConPastel.Examples.Split
