import ConPastel.Translator.Word64

/-!
# Std's bucket index on machine words

Every `Std.HashMap` operation computes its bucket with `mkIdx`:
`(scrambleHash hash).toUSize &&& (USize.ofNat sz - 1)`. A `USize` is a
`BitVec` of the platform's width, so translated, each `USize.ofNat` and each
subtraction reduces a bignum modulo `2 ^ numBits`, which dominated the
checker's profile.

`mkIdxF` computes the same index with 64-bit word operations (native in
CakeML, `ConPastel.Translator.Word64`) and builds the `USize` without a
reduction (`USize.ofNatLT`), for tables of fewer than `2 ^ 32` buckets (always,
in practice); larger tables take a copy of Std's computation (`mkIdxSlow`).
-/

namespace ConPastel.Impl
open Std.DHashMap.Internal

theorem mod_two_pow_and (a b n : Nat) (h : b < 2 ^ n) : (a % 2 ^ n) &&& b = a &&& b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hi : i < n
  · simp [hi]
  · have hb : b.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hi, hb]

/-- Std's computation, its proof by Std's. -/
def mkIdxSlow (sz : Nat) (h : 0 < sz) (hash : UInt64) : { u : USize // u.toNat < sz } :=
  ⟨(scrambleHash hash).toUSize &&& (USize.ofNat sz - 1), by
    have := (mkIdx sz h hash).2
    unfold mkIdx at this
    exact this⟩

/-- `scrambleHash` with its two shifts native (a shift by a numeral otherwise
tests the amount against words built from numerals). -/
def scrambleHashF (hash : UInt64) : UInt64 :=
  let h := hash ^^^ shr32 hash
  h ^^^ shr16 h
theorem scrambleHash_eq_F (hash : UInt64) : Std.DHashMap.Internal.scrambleHash hash = scrambleHashF hash := by
  unfold Std.DHashMap.Internal.scrambleHash scrambleHashF
  have h32 : ∀ x : UInt64, x >>> 32 = shr32 x := fun x => by apply UInt64.toBitVec_inj.mp; simp [shr32]
  have h16 : ∀ x : UInt64, x >>> 16 = shr16 x := fun x => by apply UInt64.toBitVec_inj.mp; simp [shr16]
  simp only [h32, h16]

/-- `mkIdx` on 64-bit words. -/
def mkIdxF (sz : Nat) (h : 0 < sz) (hash : UInt64) : { u : USize // u.toNat < sz } :=
  if hs : sz < 4294967296 then
    ⟨USize.ofNatLT ((scrambleHashF hash) &&& UInt64.ofNat (sz - 1)).toNat (by
        have h1 : ((scrambleHashF hash) &&& UInt64.ofNat (sz - 1)).toNat ≤ sz - 1 := by
          rw [UInt64.toNat_and, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          exact Nat.and_le_right
        have := USize.le_size
        omega),
      by
        have h1 : ((scrambleHashF hash) &&& UInt64.ofNat (sz - 1)).toNat ≤ sz - 1 := by
          rw [UInt64.toNat_and, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          exact Nat.and_le_right
        have := USize.le_size
        rw [USize.toNat_ofNatLT]
        omega⟩
  else mkIdxSlow sz h hash

theorem mkIdx_eq_F (sz : Nat) (h : 0 < sz) (hash : UInt64) : mkIdx sz h hash = mkIdxF sz h hash := by
  unfold mkIdxF
  split
  · rename_i hs
    apply Subtype.ext
    apply USize.toNat_inj.mp
    have hle := USize.le_size
    have hw := USize.size_eq_two_pow
    have hsz : sz < USize.size := by omega
    have e1 : (USize.ofNat sz).toNat = sz := by rw [USize.toNat_ofNat', ← hw, Nat.mod_eq_of_lt hsz]
    have e2 : (1 : USize).toNat = 1 := by
      show (USize.ofNat 1).toNat = 1
      rw [USize.toNat_ofNat', ← hw, Nat.mod_eq_of_lt (by omega)]
    have hle1 : (1 : USize) ≤ USize.ofNat sz := by rw [USize.le_iff_toNat_le, e1, e2]; omega
    unfold mkIdx
    rw [USize.toNat_ofNatLT, USize.toNat_and, UInt64.toNat_toUSize, USize.toNat_sub_of_le _ _ hle1, e1, e2,
      UInt64.toNat_and, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show sz - 1 < 2 ^ 64 by omega)]
    exact mod_two_pow_and _ _ _ (by rw [← hw]; omega)
  · unfold mkIdxSlow mkIdx; rfl

end ConPastel.Impl

cake_replace Std.DHashMap.Internal.mkIdx ConPastel.Impl.mkIdxF ConPastel.Impl.mkIdx_eq_F
