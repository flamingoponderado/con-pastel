import ConPastel.Translator.Replace
import ConLeche.Kernel.Expr

/-!
# con-leche's packed data word, by native shifts

`Expr.data` packs a 32-bit hash, two 15-bit ranges and a flag into a word,
read and written with multiplication, division and remainder by powers of two
(`bvarOfData w = w / 65536 % 32768`). In the translation each of those is a
fast-path test against a word built from a numeral, then the shift. Every
range test of every kernel walk reads the word, so here each field is a pair of
native shifts (`(w <<< 33) >>> 49`: bits 30…16), and the saturating range
updates compare small integers.
-/

namespace ConPastel.Impl
open ConLeche

def hashOfDataF (w : UInt64) : UInt64 := shr32 w
def bvarOfDataF (w : UInt64) : UInt64 := shr49 (shl33 w)
def fvarOfDataF (w : UInt64) : UInt64 := shr49 (shl48 w)
def lpOfDataF (w : UInt64) : Bool := (shr63 (shl63 w)).toNat == 1
def hash32F (w : UInt64) : UInt64 := shr32 (shl32 w)
def packDataF (h b f : UInt64) (lp : Bool) : UInt64 :=
  shl32 h + shl16 b + shl1 f + UInt64.ofNat (if lp then 1 else 0)
def satSuccF (n : Nat) : UInt64 := UInt64.ofNat (min (n + 1) 32767)
def satPredF (x : UInt64) : UInt64 :=
  if x.toNat = 32767 then x else if x.toNat = 0 then x else x - UInt64.ofNat 1

section
open UInt64
local macro "word_tac" : tactic => `(tactic| (
  apply UInt64.toNat_inj.mp
  simp [shr32, shr49, shr63, shl16, shl32, shl33, shl48, shl63, shl1, UInt64.toNat_shiftLeft,
    UInt64.toNat_shiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, UInt64.toNat_add,
    UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod]
  all_goals (have := UInt64.toNat_lt_size ‹UInt64›; omega)))

theorem hashOfData_eq_F (w : UInt64) : hashOfData w = hashOfDataF w := by
  unfold hashOfData hashOfDataF; word_tac
theorem bvarOfData_eq_F (w : UInt64) : bvarOfData w = bvarOfDataF w := by
  unfold bvarOfData bvarOfDataF; word_tac
theorem fvarOfData_eq_F (w : UInt64) : fvarOfData w = fvarOfDataF w := by
  unfold fvarOfData fvarOfDataF; word_tac
theorem hash32_eq_F (w : UInt64) : hash32 w = hash32F w := by
  unfold hash32 hash32F; word_tac
end

theorem lpOfData_eq_F (w : UInt64) : lpOfData w = lpOfDataF w := by
  unfold lpOfData lpOfDataF
  have h : (shr63 (shl63 w)).toNat = w.toNat % 2 := by
    simp [shr63, shl63, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    have := w.toNat_lt; omega
  rw [h]
  by_cases hw : w.toNat % 2 = 1
  · have : w % 2 = 1 := UInt64.toNat_inj.mp (by simp [UInt64.toNat_mod, hw])
    rw [this, hw]; rfl
  · have : w % 2 ≠ 1 := fun e => hw (by have := congrArg UInt64.toNat e; simpa [UInt64.toNat_mod] using this)
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr hw]

theorem packData_eq_F (h b f : UInt64) (lp : Bool) : packData h b f lp = packDataF h b f lp := by
  unfold packData packDataF
  cases lp <;> (apply UInt64.toNat_inj.mp; simp [shl16, shl32, shl1, UInt64.toNat_shiftLeft,
    Nat.shiftLeft_eq, UInt64.toNat_add, UInt64.toNat_mul]; all_goals omega)

theorem satSucc_eq_F (n : Nat) : satSucc n = satSuccF n := rfl

theorem satPred_eq_F (x : UInt64) : satPred x = satPredF x := by
  unfold satPred satPredF
  by_cases h1 : x.toNat = 32767
  · have : x = 32767 := UInt64.toNat_inj.mp (by simpa using h1)
    subst this; rfl
  by_cases h2 : x.toNat = 0
  · have : x = 0 := UInt64.toNat_inj.mp (by simpa using h2)
    subst this; rfl
  have n1 : (x == 32767) = false := by
    simp only [beq_eq_false_iff_ne]; intro e; exact h1 (by rw [e]; rfl)
  have n2 : (x == 0) = false := by
    simp only [beq_eq_false_iff_ne]; intro e; exact h2 (by rw [e]; rfl)
  simp [n1, n2, h1, h2]

end ConPastel.Impl

cake_replace ConLeche.hashOfData ConPastel.Impl.hashOfDataF ConPastel.Impl.hashOfData_eq_F
cake_replace ConLeche.bvarOfData ConPastel.Impl.bvarOfDataF ConPastel.Impl.bvarOfData_eq_F
cake_replace ConLeche.fvarOfData ConPastel.Impl.fvarOfDataF ConPastel.Impl.fvarOfData_eq_F
cake_replace ConLeche.lpOfData ConPastel.Impl.lpOfDataF ConPastel.Impl.lpOfData_eq_F
cake_replace ConLeche.hash32 ConPastel.Impl.hash32F ConPastel.Impl.hash32_eq_F
cake_replace ConLeche.packData ConPastel.Impl.packDataF ConPastel.Impl.packData_eq_F
cake_replace ConLeche.satSucc ConPastel.Impl.satSuccF ConPastel.Impl.satSucc_eq_F
cake_replace ConLeche.satPred ConPastel.Impl.satPredF ConPastel.Impl.satPred_eq_F
