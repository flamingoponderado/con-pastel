import ConPastel.Translator.Meta.RecCommand

namespace ConPastel.Examples.D1

inductive Shape where
  | dot
  | seg (a b : Nat)
  | many (n : Nat) (rest : Shape)

cake_datatype Shape

#print Shape.cakeInv
#print Shape.cakeHasCons

end ConPastel.Examples.D1
namespace ConPastel.Examples.D1
#check @Shape.many.cake_con
end ConPastel.Examples.D1
namespace ConPastel.Examples.D1
#check @Shape.cake_mat
end ConPastel.Examples.D1

namespace ConPastel.Examples.D1

def shapeSize : Shape → Nat
  | .dot => 1
  | .seg a b => a + b
  | .many n rest => n + shapeSize rest

cake_rec shapeSize
#check @shapeSize.cake_cert

def grow : Nat → Shape
  | 0 => .dot
  | n + 1 => .many n (grow n)

cake_rec grow
#print axioms grow.cake_cert

end ConPastel.Examples.D1
