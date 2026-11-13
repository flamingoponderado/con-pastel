import ConPastel.Translator.Meta.Command

/-! # First automatic translations -/

namespace ConPastel.Examples.T1

def double (x : Nat) : Nat := x + x
cake_translate double

def pick (x y : Nat) : Nat := if x < y then y * 2 else x + 1
cake_translate pick

def nested (x : Nat) : Bool := let y := x + 3; if y ≤ 10 then true else false
cake_translate nested

def higher (f : Nat → Nat) (x : Nat) : Nat := f (f x) + 1
cake_translate higher

#check @double.cake_eval
#print axioms pick.cake_eval

end ConPastel.Examples.T1
