import ConPastel.Translator.Meta.RecCommand

namespace ConPastel.Examples.T2

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

cake_rec sumTo

end ConPastel.Examples.T2

namespace ConPastel.Examples.T2
#check @sumTo.cake_cert
#print axioms sumTo.cake_cert
end ConPastel.Examples.T2
