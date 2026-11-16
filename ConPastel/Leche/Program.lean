import ConPastel.Leche.Frontend
import ConPastel.Program.Command

/-!
# The con-pastel program and its correctness

The entry point takes the input bytes (as the list of their values, the shape
the main program reads them in) and runs con-leche's pipeline on them;
`cake_program` assembles every translated unit with the main program, and
`conPastel_correct` is the final theorem: the CakeML program's verdict is
con-leche's, for every input.
-/

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.all false
set_option maxRecDepth 200000

namespace ConPastel

theorem byteArray_toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  induction h : bs.size - i generalizing i r with
  | zero =>
    unfold ByteArray.toList.loop
    have : ¬ i < bs.size := by omega
    simp only [this, ite_false]
    have : bs.data.toList.length ≤ i := by
      rw [Array.length_toList]; exact Nat.le_of_not_lt this
    simp [List.drop_eq_nil_of_le this]
  | succ n ih =>
    unfold ByteArray.toList.loop
    have hi : i < bs.size := by omega
    simp only [hi, ite_true]
    rw [ih (i+1) _ (by omega)]
    have hi2 : i < bs.data.size := hi
    have hi' : i < bs.data.toList.length := by rw [Array.length_toList]; exact hi2
    simp [ByteArray.get!, List.drop_eq_getElem_cons hi', getElem!_def, Array.getElem?_eq_getElem hi2]

theorem byteArray_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  simp [ByteArray.toList, byteArray_toList_loop]

/-- The input file from the values of its bytes. -/
def entryOf (bs : List Nat) : ByteArray := ⟨⟨bs.map UInt8.ofNat⟩⟩

theorem entryOf_input (input : ByteArray) : entryOf (input.toList.map UInt8.toNat) = input := by
  rcases input with ⟨⟨l⟩⟩
  simp [entryOf, byteArray_toList, Function.comp_def]

/-- The checker on the values of the input bytes. -/
def conPastelEntry (bs : List Nat) : Bool := conLecheAccepts (entryOf bs)

cake_unit conPastelEntry
cake_program conPastelP conPastelEntry

/-- The CakeML program. -/
def conPastelProg : List Flapjack.AstHOL.Dec := conPastelP.prog

/-- **con-pastel's correctness**: under the runtime assumptions, for every
input file the CakeML program terminates, and only terminates, writing
con-leche's verdict. -/
theorem conPastel_correct (h : RuntimeAssumptions) : Implements conPastelProg :=
  implementsRef_of_completes _ _ fun input => by
    obtain ⟨events, hc, hw⟩ := conPastelP.correct h input
    exact ⟨events, hc, by rw [hw, conPastelEntry, entryOf_input]⟩

#print axioms conPastel_correct

end ConPastel
