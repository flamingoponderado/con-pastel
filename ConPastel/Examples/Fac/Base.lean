import ConPastel.Program.Command

/-! # Factored translation: the common base (datatypes and shared units) -/

namespace ConPastel.Examples.Fac
def countBig (l : List Nat) : Nat := (l.filter (· > 100)).length
cake_datatype (Option Nat)
cake_unit (@List.length Nat)
end ConPastel.Examples.Fac
