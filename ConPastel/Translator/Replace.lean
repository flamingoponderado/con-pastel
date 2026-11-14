import ConPastel.Translator.Prims

/-! # Replacements for library functions whose definitions do not translate -/

namespace ConPastel.Impl

/-- `UInt8.utf8ByteSize` without its proof argument. -/
def utf8Size (c : UInt8) : Nat :=
  if c &&& 128 = 0 then 1 else if c &&& 224 = 192 then 2 else if c &&& 240 = 224 then 3 else 4

theorem utf8Size_pos (c : UInt8) : 0 < utf8Size c := by
  unfold utf8Size; split <;> (try split) <;> (try split) <;> omega

open ByteArray.utf8DecodeChar? in
/-- `ByteArray.validateUTF8At` without proof-carrying matches. -/
def validateAt (b : ByteArray) (i : Nat) : Bool :=
  if h₀ : i < b.size then
    match parseFirstByte b[i] with
    | .invalid => false
    | .done => true
    | .oneMore => if h₁ : i + 1 < b.size then verify₂ b[i] b[i + 1] else false
    | .twoMore => if h₁ : i + 2 < b.size then verify₃ b[i] b[i + 1] b[i + 2] else false
    | .threeMore => if h₁ : i + 3 < b.size then verify₄ b[i] b[i + 1] b[i + 2] b[i + 3] else false
  else false

theorem validateAt_eq (b : ByteArray) (i : Nat) : b.validateUTF8At i = validateAt b i := by
  unfold ByteArray.validateUTF8At validateAt
  split
  · split <;> simp_all [ByteArray.utf8DecodeChar?.verify₁]
  · rfl

/-- `ByteArray.validateUTF8.go` without its proof argument. -/
def validateGo (b : ByteArray) (i : Nat) : Bool :=
  if h : i < b.size then
    if validateAt b i then validateGo b (i + utf8Size b[i]) else false
  else true
termination_by b.size - i
decreasing_by have := utf8Size_pos b[i]; omega

theorem validateGo_eq (b : ByteArray) (i : Nat) (hi : i ≤ b.size) :
    ByteArray.validateUTF8.go b i hi = validateGo b i := by
  rw [ByteArray.validateUTF8.go.eq_def, validateGo.eq_def]
  by_cases h : i < b.size
  · simp only [h, dite_eq_left]
    split
    · rename_i h'; simp [← validateAt_eq, h']
    · rename_i h'
      simp only [← validateAt_eq, h', ite_true]
      exact validateGo_eq b _ _
  · simp [h]
termination_by b.size - i
decreasing_by
  all_goals
    have := utf8Size_pos b[i]
    unfold utf8Size at this
    simp only [UInt8.utf8ByteSize]
    omega

/-- `ByteArray.validateUTF8` via `validateGo`. -/
def validateUTF8 (b : ByteArray) : Bool := validateGo b 0

theorem validateUTF8_eq (b : ByteArray) : ByteArray.validateUTF8 b = validateUTF8 b :=
  validateGo_eq b 0 (Nat.zero_le _)

/-- `Array.range` via `List.range` (`Array.ofFn.go` recurses with a proof parameter). -/
def arrayRange (n : Nat) : Array Nat := ⟨List.range n⟩

theorem arrayRange_eq (n : Nat) : Array.range n = arrayRange n := by
  apply Array.ext'; simp [arrayRange]

end ConPastel.Impl

cake_replace ByteArray.validateUTF8 ConPastel.Impl.validateUTF8 ConPastel.Impl.validateUTF8_eq
cake_replace Array.range ConPastel.Impl.arrayRange ConPastel.Impl.arrayRange_eq
