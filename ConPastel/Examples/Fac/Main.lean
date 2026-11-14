import ConPastel.Examples.Fac.LeafA
import ConPastel.Examples.Fac.LeafB

/-! # Factored translation: assembling independent leaves -/

namespace ConPastel.Examples.Fac
def both (l : List Nat) : Bool := lenEven l && headSmall l
cake_module "FacMain"
cake_unit both
cake_program fac both
#print axioms fac.correct
end ConPastel.Examples.Fac
