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
end ConPastel.Impl

cake_replace ByteArray.validateUTF8 ConPastel.Impl.validateUTF8 ConPastel.Impl.validateUTF8_eq
cake_replace Array.range ConPastel.Impl.arrayRange ConPastel.Impl.arrayRange_eq
cake_replace instDecidableEqString ConPastel.Impl.stringDecEq ConPastel.Impl.stringDecEq_eq
cake_replace ByteArray.utf8Decode? ConPastel.Impl.utf8Decode ConPastel.Impl.utf8Decode_eq
cake_replace ByteArray.utf8DecodeChar? ConPastel.Impl.decodeChar ConPastel.Impl.decodeChar_eq
cake_replace String.foldl ConPastel.Impl.stringFoldl ConPastel.Impl.stringFoldl_eq
cake_replace List.nodupDecidable ConPastel.Impl.nodupDec ConPastel.Impl.nodupDec_eq
