import ConPastel.Program.Command
import ConPastel.Translator.Replace
import Std.Data.HashMap

/-! # Arrays as Braun trees, and a `HashMap` over them -/

namespace ConPastel.Examples.Arrays

def fill (n : Nat) : Array Nat := Id.run do
  let mut a : Array Nat := #[]
  for i in [0:n] do a := a.push (i * i)
  return a

def bump (a : Array Nat) (i : Nat) : Array Nat := a.setIfInBounds i (a.getD i 0 + 1)

def table (l : List Nat) : Std.HashMap Nat Nat := l.foldl (fun m x => m.insert x (x + 1)) {}

def check (l : List Nat) : Bool :=
  let a := bump (fill l.length) 2
  let m := table l
  a.size == l.length && a[3]! == 9 && m.get? 5 == some 6 && m.contains 7

cake_unit check
cake_program arrays check
#print axioms arrays.correct

end ConPastel.Examples.Arrays
