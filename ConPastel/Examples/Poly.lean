import ConPastel.Translator.Meta.Unit

namespace ConPastel.Examples.Poly

def myLen {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => 1 + myLen xs

cake_unit (@myLen Nat)

def useLen (xs : List Nat) : Nat := myLen xs + 1
cake_unit useLen

cake_unit (@List.length Nat) (@List.map Nat Nat)

def bump (xs : List Nat) : List Nat := xs.map (fun x => x + 1)
cake_unit bump

#check @ConPastel.Cake.u1.cert
#print axioms ConPastel.Cake.u4.cert

end ConPastel.Examples.Poly
