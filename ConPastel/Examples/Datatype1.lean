import ConPastel.Translator.Meta.Datatype

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
