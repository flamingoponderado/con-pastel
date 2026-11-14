import ConPastel.Examples.Fac.Base

/-! # Factored translation: an independent leaf -/

cake_module "FacA"
namespace ConPastel.Examples.Fac
def lenEven (l : List Nat) : Bool := l.length % 2 == 0
cake_unit lenEven
end ConPastel.Examples.Fac
