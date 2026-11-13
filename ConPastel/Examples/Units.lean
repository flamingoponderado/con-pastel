import ConPastel.Translator.Meta.Unit

namespace ConPastel.Examples.U

def sq (x : Nat) : Nat := x * x
def sumSq : Nat → Nat
  | 0 => 0
  | n + 1 => sq (n + 1) + sumSq n
def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
def useBoth (x : Nat) : Nat := twice sq x + sumSq x
def addAcc : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => addAcc n (acc + sq n)
def seven : Nat := 3 + 4
def callAcc (x : Nat) : Nat := addAcc x seven + 2

cake_unit sq sumSq twice useBoth addAcc seven callAcc

#check @useBoth.cake_cert
#check @callAcc.cake_cert
#print axioms callAcc.cake_cert

end ConPastel.Examples.U
