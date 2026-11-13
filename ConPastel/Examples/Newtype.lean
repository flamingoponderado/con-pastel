import ConPastel.Translator.Meta.Datatype

namespace ConPastel.Examples.NT

structure Box where
  val : Nat
  pos : val > 0

def unbox (b : Box) : Nat := b.val + 1
cake_unit unbox

def mkBox (n : Nat) : Box := ⟨n + 1, by omega⟩
cake_unit mkBox

def boxSum (b c : Box) : Nat := match b with | ⟨x, _⟩ => x + c.val
cake_unit boxSum

def finVal (i : Fin 10) : Nat := i.val * 2
cake_unit finVal

def subVal (x : {n : Nat // n < 5}) : Nat := x.1 + 1
cake_unit subVal

#print axioms ConPastel.Cake.u4.cert

end ConPastel.Examples.NT
