import ConPastel.Translator.Prims
import ConPastel.Translator.Word
import ConPastel.Translator.Word64
import ConPastel.Translator.FastIdx
import ConPastel.Translator.ArrayB
import ConPastel.Spec

/-! # Replacements for library functions whose definitions do not translate -/

cake_alias ConPastel.Impl.npGo ConPastel.Impl.npGo_eq "_private.Init.Data.Nat.Power2.Basic.0.Nat.nextPowerOfTwo.go"

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

/-- String equality by a structural byte comparison (`instDecidableEqString`
goes through `List`'s dependent `DecidableEq`). -/
def bytesEq : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | a :: as, b :: bs => a == b && bytesEq as bs
  | _, _ => false

theorem bytesEq_iff : ∀ (x y : List UInt8), bytesEq x y = true ↔ x = y
  | [], [] => by simp [bytesEq]
  | [], _ :: _ => by simp [bytesEq]
  | _ :: _, [] => by simp [bytesEq]
  | a :: as, b :: bs => by simp [bytesEq, bytesEq_iff as bs]

theorem string_eq_iff_bytes (a b : String) :
    a.toByteArray.data.toList = b.toByteArray.data.toList ↔ a = b := by
  constructor
  · intro h
    cases a; cases b
    simp only [String.ofByteArray.injEq]
    cases ‹ByteArray›; cases ‹ByteArray›
    simp_all
  · intro h; rw [h]

def stringDecEq (a b : String) : Decidable (a = b) :=
  if h : bytesEq a.toByteArray.data.toList b.toByteArray.data.toList = true then
    isTrue ((string_eq_iff_bytes a b).mp ((bytesEq_iff _ _).mp h))
  else isFalse (fun e => h ((bytesEq_iff _ _).mpr ((string_eq_iff_bytes a b).mpr e)))

theorem stringDecEq_eq (a b : String) : instDecidableEqString a b = stringDecEq a b :=
  Subsingleton.elim _ _
/-- `ByteArray.utf8Decode?` without the proof parameter of its loop. -/
def decodeGo (b : ByteArray) (i : Nat) (acc : Array Char) : Option (Array Char) :=
  if i < b.size then
    match b.utf8DecodeChar? i with
    | none => none
    | some c => decodeGo b (i + c.utf8Size) (acc.push c)
  else some acc
termination_by b.size - i
decreasing_by have := Char.utf8Size_pos c; omega

theorem decodeGo_eq (b : ByteArray) (i : Nat) (acc : Array Char) (hi : i ≤ b.size) :
    ByteArray.utf8Decode?.go b i acc hi = decodeGo b i acc := by
  rw [ByteArray.utf8Decode?.go.eq_def, decodeGo.eq_def]
  by_cases h : i < b.size
  · simp only [h, ite_true]
    split
    · rename_i h'; simp [h']
    · rename_i c h'
      simp only [h']
      exact decodeGo_eq b _ _ _
  · simp [h]
termination_by b.size - i
decreasing_by all_goals (expose_names; have := Char.utf8Size_pos c; omega)

def utf8Decode (b : ByteArray) : Option (Array Char) := decodeGo b 0 #[]
theorem utf8Decode_eq (b : ByteArray) : ByteArray.utf8Decode? b = utf8Decode b :=
  decodeGo_eq b 0 #[] (Nat.zero_le _)
open ByteArray.utf8DecodeChar? in
/-- `FirstByte.done` as a Boolean test. -/
def isDone : FirstByte → Bool
  | .done => true
  | _ => false

open ByteArray.utf8DecodeChar? in
theorem eq_done_of_isDone {f : FirstByte} (h : isDone f = true) : f = .done := by
  cases f <;> simp_all [isDone]

open ByteArray.utf8DecodeChar? in
/-- `ByteArray.utf8DecodeChar?` without the equation-carrying match. -/
def decodeChar (bytes : ByteArray) (i : Nat) : Option Char :=
  if h₀ : i < bytes.size then
    match parseFirstByte bytes[i] with
    | .invalid => none
    | .done => if h : isDone (parseFirstByte bytes[i]) = true then assemble₁ bytes[i] (eq_done_of_isDone h) else none
    | .oneMore => if h₁ : i + 1 < bytes.size then assemble₂ bytes[i] bytes[i + 1] else none
    | .twoMore => if h₁ : i + 2 < bytes.size then assemble₃ bytes[i] bytes[i + 1] bytes[i + 2] else none
    | .threeMore =>
      if h₁ : i + 3 < bytes.size then assemble₄ bytes[i] bytes[i + 1] bytes[i + 2] bytes[i + 3] else none
  else none

theorem decodeChar_eq (bytes : ByteArray) (i : Nat) : bytes.utf8DecodeChar? i = decodeChar bytes i := by
  unfold ByteArray.utf8DecodeChar? decodeChar
  split
  · split <;> simp_all [isDone]
  · rfl
/-- `String.foldl` over the character list (the library goes through `String.Slice`). -/
def stringFoldl {α : Type u} (f : α → Char → α) (init : α) (s : String) : α := s.toList.foldl f init

theorem stringFoldl_eq {α : Type u} (f : α → Char → α) (init : α) (s : String) :
    String.foldl f init s = stringFoldl f init s := by
  simp [stringFoldl, String.foldl_eq_foldl_toList]

/-- Duplicate-freeness as a Boolean recursion. -/
def nodupB {α : Type u} [DecidableEq α] : List α → Bool
  | [] => true
  | a :: as => !(as.elem a) && nodupB as

theorem nodupB_iff {α : Type u} [DecidableEq α] : ∀ (l : List α), nodupB l = true ↔ l.Nodup
  | [] => by simp [nodupB]
  | a :: as => by simp [nodupB, nodupB_iff as, List.nodup_cons]

def nodupDec {α : Type u} [DecidableEq α] (l : List α) : Decidable l.Nodup :=
  if h : nodupB l = true then isTrue ((nodupB_iff l).mp h)
  else isFalse (fun e => h ((nodupB_iff l).mpr e))

theorem nodupDec_eq {α : Type u} [DecidableEq α] (l : List α) : List.nodupDecidable l = nodupDec l :=
  Subsingleton.elim _ _
/-- `Nat.nextPowerOfTwo`'s loop without its proof parameter. -/
def np2Go (n power : Nat) : Nat :=
  if 0 < power ∧ power < n then np2Go n (power * 2) else power
termination_by n - power

theorem np2Go_eq (n power : Nat) (h : power > 0) : npGo n power h = np2Go n power := by
  delta npGo; rw [npGo_eq, np2Go.eq_def]
  by_cases hp : power < n
  · simp only [hp, h, and_self, ite_true]
    exact np2Go_eq n (power * 2) (by omega)
  · simp [hp]
termination_by n - power

def nextPowerOfTwo (n : Nat) : Nat := np2Go n 1
theorem nextPowerOfTwo_eq (n : Nat) : Nat.nextPowerOfTwo n = nextPowerOfTwo n :=
  np2Go_eq n 1 (by decide)
/-- `Array.foldlM` (default bounds) over the list (`Array.foldlM.loop` carries proofs). -/
theorem arrayFoldlM_eq {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}
    (f : β → α → m β) (init : β) (as : Array α) :
    as.foldlM f init 0 as.size = as.toList.foldlM f init := (Array.foldlM_toList ..).symm

/-- `Nat.log2` by plain recursion (the library's is a fuelled `Nat.rec`). -/
def log2 (n : Nat) : Nat := if 2 ≤ n then log2 (n / 2) + 1 else 0
termination_by n
decreasing_by omega

theorem log2_eq (n : Nat) : Nat.log2 n = log2 n := by
  rw [Nat.log2_def, log2.eq_def]
  split
  · rename_i h; rw [log2_eq (n / 2)]
  · rfl
termination_by n
decreasing_by omega
/-- `Array.eraseIdx` via the list (its loop recurses with a proof parameter). -/
theorem arrayEraseIdx_eq {α : Type u} (a : Array α) (i : Nat) (h : i < a.size) :
    a.eraseIdx i h = ⟨a.toList.eraseIdx i⟩ := by
  apply Array.ext'; simp

/-! `Array` operations over the list (core `Array` loops recurse with proof parameters). -/
section ArrayOps
variable {α : Type u} {β : Type v}
theorem arrayFoldl_eq (f : β → α → β) (init : β) (as : Array α) :
    as.foldl f init 0 as.size = as.toList.foldl f init := (Array.foldl_toList ..).symm
theorem arrayFoldr_eq (f : α → β → β) (init : β) (as : Array α) :
    as.foldr f init as.size 0 = as.toList.foldr f init := (Array.foldr_toList ..).symm
theorem arrayAny_eq (as : Array α) (p : α → Bool) : as.any p 0 as.size = as.toList.any p := by simp
theorem arrayAll_eq (as : Array α) (p : α → Bool) : as.all p 0 as.size = as.toList.all p := by simp
theorem arrayContains_eq [BEq α] (as : Array α) (a : α) : as.contains a = as.toList.contains a := by simp
theorem arrayFilter_eq (p : α → Bool) (as : Array α) : as.filter p 0 as.size = ⟨as.toList.filter p⟩ := by
  apply Array.ext'; simp
theorem arrayFilterMap_eq (f : α → Option β) (as : Array α) : as.filterMap f 0 as.size = ⟨as.toList.filterMap f⟩ := by
  apply Array.ext'; simp
theorem arrayFlatMap_eq (f : α → Array β) (as : Array α) : as.flatMap f = ⟨as.toList.flatMap (fun x => (f x).toList)⟩ := by
  apply Array.ext'; simp
theorem arrayAppend_eq (as bs : Array α) : as ++ bs = ⟨as.toList ++ bs.toList⟩ := by apply Array.ext'; simp
theorem arrayReverse_eq (as : Array α) : as.reverse = ⟨as.toList.reverse⟩ := by apply Array.ext'; simp
theorem arrayFind?_eq (p : α → Bool) (as : Array α) : as.find? p = as.toList.find? p := by simp
theorem arrayMapIdx_eq (f : Nat → α → β) (as : Array α) : as.mapIdx f = ⟨as.toList.mapIdx f⟩ := by apply Array.ext'; simp
end ArrayOps

/-! Conditionals applied to further arguments (e.g. a monadic state): push the
arguments into the branches. -/
theorem dite_app {α : Sort u} {β : α → Sort v} (P : Prop) [Decidable P] (f : P → (a : α) → β a)
    (g : ¬P → (a : α) → β a) (a : α) : dite P f g a = dite P (fun h => f h a) (fun h => g h a) := by
  by_cases h : P <;> simp [h]
theorem ite_app {α : Sort u} {β : α → Sort v} (P : Prop) [Decidable P] (f g : (a : α) → β a) (a : α) :
    ite P f g a = ite P (f a) (g a) := by
  by_cases h : P <;> simp [h]
theorem cond_app {α : Sort u} {β : α → Sort v} (b : Bool) (f g : (a : α) → β a) (a : α) :
    cond b f g a = cond b (f a) (g a) := by
  cases b <;> rfl

end ConPastel.Impl

cake_replace ByteArray.validateUTF8 ConPastel.Impl.validateUTF8 ConPastel.Impl.validateUTF8_eq
cake_replace Array.range ConPastel.Impl.arrayRange ConPastel.Impl.arrayRange_eq
cake_replace instDecidableEqString ConPastel.Impl.stringDecEq ConPastel.Impl.stringDecEq_eq
cake_replace ByteArray.utf8Decode? ConPastel.Impl.utf8Decode ConPastel.Impl.utf8Decode_eq
cake_replace ByteArray.utf8DecodeChar? ConPastel.Impl.decodeChar ConPastel.Impl.decodeChar_eq
cake_replace String.foldl ConPastel.Impl.stringFoldl ConPastel.Impl.stringFoldl_eq
cake_replace List.nodupDecidable ConPastel.Impl.nodupDec ConPastel.Impl.nodupDec_eq

cake_replace Nat.log2 ConPastel.Impl.log2 ConPastel.Impl.log2_eq
cake_replace Nat.nextPowerOfTwo ConPastel.Impl.nextPowerOfTwo ConPastel.Impl.nextPowerOfTwo_eq

/-! Opaque runtime primitives, under `RuntimeAssumptions` (their transcriptions
are checked against the runtime by `scripts/HashCheck.lean`). -/
cake_replace_assuming mixHash ConPastel.leanMixHash (∀ h k, mixHash h k = ConPastel.leanMixHash h k)
cake_replace_assuming String.hash ConPastel.leanStringHash (∀ s, String.hash s = ConPastel.leanStringHash s)
cake_rewrite ConPastel.Impl.arrayFoldlM_eq

/-! con-leche's errors only decide that a file is rejected: nothing inspects
an error's contents (they are rethrown, paired with a position, or dropped),
so `CheckError` is a ghost type. This is how the opaque `partial def
Expr.hasStrLitGo` (it only picks an error's kind) needs no assumption. -/
cake_ghost ConLeche.CheckError

/-! con-leche's memoized expression walks: the result of a walk is fixed by its
subtype (`resTerm_eq`), so the plain recursive specification is translated in
place of the memo machinery (same results; the memo only saves work). -/
cake_rewrite ConLeche.Expr.resTerm_eq
cake_rewrite ConLeche.Expr.resBool_eq
cake_rewrite ConLeche.Expr.resNat_eq
cake_rewrite ConPastel.Impl.arrayEraseIdx_eq

cake_rewrite ConPastel.Impl.arrayFoldl_eq
cake_rewrite ConPastel.Impl.arrayFoldr_eq
cake_rewrite ConPastel.Impl.arrayAny_eq
cake_rewrite ConPastel.Impl.arrayAll_eq
cake_rewrite ConPastel.Impl.arrayContains_eq
cake_rewrite ConPastel.Impl.arrayFilter_eq
cake_rewrite ConPastel.Impl.arrayFilterMap_eq
cake_rewrite ConPastel.Impl.arrayFlatMap_eq
cake_rewrite ConPastel.Impl.arrayAppend_eq
cake_rewrite ConPastel.Impl.arrayReverse_eq
cake_rewrite ConPastel.Impl.arrayFind?_eq
cake_rewrite ConPastel.Impl.arrayMapIdx_eq
cake_rewrite ConPastel.Impl.dite_app
cake_rewrite ConPastel.Impl.ite_app
cake_rewrite ConPastel.Impl.cond_app

/-! ## `mixHash` without bignums

`leanMixHash` multiplies by `0xc6a4a7935bd1e995`, above the small-integer
range: as a literal it is a bignum converted to a word at every call.
`leanMixHashF` multiplies by its 22-bit limbs and builds it from two 32-bit
halves for the `xor`. -/

namespace ConPastel.Impl

/-- `mulL` with the second operand given by its limbs. -/
def mulLc (a : UInt64) (b0 b1 b2 : Nat) : UInt64 :=
  let a0 := (a &&& UInt64.ofNat 4194303).toNat
  let a1 := (shr22 a &&& UInt64.ofNat 4194303).toNat
  let a2 := (shr44 a).toNat
  UInt64.ofNat (a0 * b0) + shl22 (UInt64.ofNat (a0 * b1 + a1 * b0)) +
    shl44 (UInt64.ofNat (a0 * b2 + a1 * b1 + a2 * b0))

/-- Multiplication by `0xc6a4a7935bd1e995`, by its limbs (small integers). -/
def mulMix (a : UInt64) : UInt64 := mulLc a 1173909 1985903 813642

theorem mulMix_eq (a : UInt64) : a * 0xc6a4a7935bd1e995 = mulMix a := by
  rw [show a * 0xc6a4a7935bd1e995 = u64mulP a 0xc6a4a7935bd1e995 from rfl, mulL_eq]
  rfl

/-- `leanMixHash` without materialising its constant as a bignum: the
multiplications by its limbs, the `xor` with it built from two 32-bit halves,
the shift by 47 native. -/
def leanMixHashF (h k : UInt64) : UInt64 :=
  let m : UInt64 := shl32 (UInt64.ofNat 3332679571) + UInt64.ofNat 1540483477
  let k := mulMix k
  let k := k ^^^ shr47 k
  let k := k ^^^ m
  mulMix (h ^^^ k)

theorem leanMixHash_eq_F (h k : UInt64) : ConPastel.leanMixHash h k = leanMixHashF h k := by
  unfold ConPastel.leanMixHash leanMixHashF
  simp only [← mulMix_eq]
  have hm : shl32 (UInt64.ofNat 3332679571) + UInt64.ofNat 1540483477 = 0xc6a4a7935bd1e995 := by decide
  have h47 : ∀ x : UInt64, x >>> 47 = shr47 x := fun x => by
    apply UInt64.toBitVec_inj.mp; simp [shr47]
  rw [hm, h47]

end ConPastel.Impl

cake_replace ConPastel.leanMixHash ConPastel.Impl.leanMixHashF ConPastel.Impl.leanMixHash_eq_F
