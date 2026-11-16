import ConPastel.Program.Command
import ConPastel.Translator.Replace

/-! # Fixed-width arithmetic through `Word64` primitives -/

namespace ConPastel.Examples.Words

def mix (h : UInt64) (x : Nat) : UInt64 :=
  let m : UInt64 := 0xc6a4a7935bd1e995
  let k : UInt64 := x.toUInt64 * m
  let k : UInt64 := k ^^^ (k >>> (47 : UInt64))
  ((h ^^^ k) * m + (h <<< (3 : UInt64))) ||| (k &&& (0xff : UInt64))

def check (l : List Nat) : Bool := (l.foldl mix 11).toNat % 3 == 1

cake_unit check
cake_program words check
#print axioms words.correct

end ConPastel.Examples.Words
