import ConPastel.Examples.Fac.Base

/-! # Factored translation: another independent leaf (shares `List.length` via the base,
and translates `List.reverse` on its own) -/

cake_module "FacB"
namespace ConPastel.Examples.Fac
def headSmall (l : List Nat) : Bool := match l.reverse.head? with | some x => x < 100 | none => l.length == 0
cake_unit headSmall
end ConPastel.Examples.Fac
