import ConPastel.Translator.Meta.RecCommand

namespace ConPastel.Examples.T3

def addAcc : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => addAcc n (acc + n + 1)

cake_recn addAcc
#check @addAcc.cake_cert
#print axioms addAcc.cake_cert

end ConPastel.Examples.T3
