import ConPastel.Translator.Prims

/-!
# Fast fixed-width arithmetic

Lean's runtime implements `UInt64`, `BitVec` and the bitwise `Nat` operations
with machine instructions, but their definitions are recursions (`Nat.bitwise`
recurses once per bit, `Nat.pow` once per exponent unit), and every `UInt64`
operation reduces modulo `2 ^ 64`. Translated literally they dominate
con-leche's run time (hashing). This file gives:

* `Word64` primitives `xor64`/`and64`/`or64`: convert both operands to CakeML
  64-bit words, apply the native instruction, convert back;
* replacements (`cake_replace`) for `Nat.xor`/`Nat.land`/`Nat.lor` that use them
  when both operands are below `2 ^ 64`, and for `Nat.pow` by squaring, with
  the powers of two used by fixed-width types as literals.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString

/-! ## Unary primitives and words -/

/-- A pure unary primitive. -/
theorem Eval_unop {env : SemEnv Value} {op : Op} {e : Exp} {P Q : Value → Prop}
    (hclass : getOpClass op = .simple) (h : Eval env e P)
    (hop : ∀ v, P v → ∃ w, Q w ∧
      ∀ {σ : Type} (refs : Store Value) (ffi : HolFfiState σ),
        doApp (refs, ffi) op [v] = some ((refs, ffi), .val w)) :
    Eval env (.app op [e]) Q := by
  intro σ s
  obtain ⟨v, r, hv, pv⟩ := h σ s
  obtain ⟨w, qw, hdo⟩ := hop v pv
  refine ⟨w, r, ?_, qw⟩
  obtain ⟨a₁, a₂, ha⟩ := hv.runs
  refine ⟨a₁, a₂, ?_⟩
  have := evaluate_app_simple (args := [e]) (by simpa using ha) hclass (hdo _ _)
  simpa [listResult] using this

/-- A CakeML 64-bit word. -/
def W64 : RefInv (BitVec 64) := fun w v => v = .litv (.word64 w)

theorem Eval_int_to_w64 {env : SemEnv Value} {e : Exp} {i : Int} (h : Eval env e (INT i)) :
    Eval env (.app (.fromTo .intT (.wordT .w64)) [e]) (W64 (BitVec.ofInt 64 i)) :=
  Eval_unop rfl h fun v hv => by
    subst hv
    exact ⟨_, rfl, fun refs ffi => by
      simp [doApp_fromTo_core, doAppNumericCore_fromTo, checkType, doConversion, theLitvInt]⟩

theorem Eval_w64_to_int {env : SemEnv Value} {e : Exp} {w : BitVec 64} (h : Eval env e (W64 w)) :
    Eval env (.app (.fromTo (.wordT .w64) .intT) [e]) (INT w.toNat) :=
  Eval_unop rfl h fun v hv => by
    subst hv
    exact ⟨_, rfl, fun refs ffi => by
      simp [doApp_fromTo_core, doAppNumericCore_fromTo, checkType, doConversion, theLitvWord64]⟩

theorem Eval_w64_xor {env : SemEnv Value} {e₁ e₂ : Exp} {a b : BitVec 64}
    (h₁ : Eval env e₁ (W64 a)) (h₂ : Eval env e₂ (W64 b)) :
    Eval env (.app (.arith .xor (.wordT .w64)) [e₁, e₂]) (W64 (a ^^^ b)) :=
  Eval_binop rfl h₁ h₂ fun v₁ v₂ p₁ p₂ => by
    subst p₁ p₂
    exact ⟨_, rfl, fun refs ffi => by simp [doApp_arith_core, doAppNumericCore, wordArith]⟩

theorem Eval_w64_and {env : SemEnv Value} {e₁ e₂ : Exp} {a b : BitVec 64}
    (h₁ : Eval env e₁ (W64 a)) (h₂ : Eval env e₂ (W64 b)) :
    Eval env (.app (.arith .and (.wordT .w64)) [e₁, e₂]) (W64 (a &&& b)) :=
  Eval_binop rfl h₁ h₂ fun v₁ v₂ p₁ p₂ => by
    subst p₁ p₂
    exact ⟨_, rfl, fun refs ffi => by simp [doApp_arith_core, doAppNumericCore, wordArith]⟩

theorem Eval_w64_or {env : SemEnv Value} {e₁ e₂ : Exp} {a b : BitVec 64}
    (h₁ : Eval env e₁ (W64 a)) (h₂ : Eval env e₂ (W64 b)) :
    Eval env (.app (.arith .or (.wordT .w64)) [e₁, e₂]) (W64 (a ||| b)) :=
  Eval_binop rfl h₁ h₂ fun v₁ v₂ p₁ p₂ => by
    subst p₁ p₂
    exact ⟨_, rfl, fun refs ffi => by simp [doApp_arith_core, doAppNumericCore, wordArith]⟩

/-- `fromTo intT w64` of a variable holding `NAT x`. -/
def toW (x : String) : Exp := .app (.fromTo .intT (.wordT .w64)) [V x]

/-- The body of a word primitive: `fn b => w2i (op (i2w p) (i2w b))`. -/
def wordBody (op : Arith) : Exp :=
  .fn (ofString "b") (.app (.fromTo (.wordT .w64) .intT) [.app (.arith op (.wordT .w64)) [toW "p", toW "b"]])

end ConPastel.Translator

namespace ConPastel.Impl

/-- `xor` of the low 64 bits. -/
def xor64 (a b : Nat) : Nat := (BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b).toNat
/-- `and` of the low 64 bits. -/
def and64 (a b : Nat) : Nat := (BitVec.ofNat 64 a &&& BitVec.ofNat 64 b).toNat
/-- `or` of the low 64 bits. -/
def or64 (a b : Nat) : Nat := (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b).toNat

end ConPastel.Impl

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive ConPastel.Impl.xor64 (wordBody .xor) by
  intro envC funs hnodup hfind _ _ _
  refine prim2_cert envC funs _ hnodup hfind ?_
  intro x xv y yv hx hy
  obtain ⟨ha, hb⟩ := prim_args envC funs x y xv yv hx hy
  exact Eval_weaken (Eval_w64_to_int (Eval_w64_xor (Eval_int_to_w64 ha) (Eval_int_to_w64 hb)))
    fun w hw => by simp only [INT] at hw; simp [NAT, hw, ConPastel.Impl.xor64, BitVec.ofInt_natCast]

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive ConPastel.Impl.and64 (wordBody .and) by
  intro envC funs hnodup hfind _ _ _
  refine prim2_cert envC funs _ hnodup hfind ?_
  intro x xv y yv hx hy
  obtain ⟨ha, hb⟩ := prim_args envC funs x y xv yv hx hy
  exact Eval_weaken (Eval_w64_to_int (Eval_w64_and (Eval_int_to_w64 ha) (Eval_int_to_w64 hb)))
    fun w hw => by simp only [INT] at hw; simp [NAT, hw, ConPastel.Impl.and64, BitVec.ofInt_natCast]

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive ConPastel.Impl.or64 (wordBody .or) by
  intro envC funs hnodup hfind _ _ _
  refine prim2_cert envC funs _ hnodup hfind ?_
  intro x xv y yv hx hy
  obtain ⟨ha, hb⟩ := prim_args envC funs x y xv yv hx hy
  exact Eval_weaken (Eval_w64_to_int (Eval_w64_or (Eval_int_to_w64 ha) (Eval_int_to_w64 hb)))
    fun w hw => by simp only [INT] at hw; simp [NAT, hw, ConPastel.Impl.or64, BitVec.ofInt_natCast]

namespace ConPastel.Impl

/-! ## Replacements -/

/-- `2 ^ 64`. -/
abbrev two64 : Nat := 18446744073709551616

/-- `Nat.xor`, on machine words when both operands fit. -/
def natXor (a b : Nat) : Nat := if a < two64 ∧ b < two64 then xor64 a b else Nat.bitwise bne a b
/-- `Nat.land`, on machine words when both operands fit. -/
def natLand (a b : Nat) : Nat := if a < two64 ∧ b < two64 then and64 a b else Nat.bitwise and a b
/-- `Nat.lor`, on machine words when both operands fit. -/
def natLor (a b : Nat) : Nat := if a < two64 ∧ b < two64 then or64 a b else Nat.bitwise or a b

theorem natXor_eq (a b : Nat) : Nat.xor a b = natXor a b := by
  unfold natXor; split
  · rename_i h
    simp [xor64, BitVec.toNat_xor, Nat.mod_eq_of_lt h.1, Nat.mod_eq_of_lt h.2]
  · rfl

theorem natLand_eq (a b : Nat) : Nat.land a b = natLand a b := by
  unfold natLand; split
  · rename_i h
    simp [and64, BitVec.toNat_and, Nat.mod_eq_of_lt h.1, Nat.mod_eq_of_lt h.2]
  · rfl

theorem natLor_eq (a b : Nat) : Nat.lor a b = natLor a b := by
  unfold natLor; split
  · rename_i h
    simp [or64, BitVec.toNat_or, Nat.mod_eq_of_lt h.1, Nat.mod_eq_of_lt h.2]
  · rfl

/-- `b ^ e` by squaring. -/
def powSq (b e : Nat) : Nat :=
  if e = 0 then 1
  else
    let h := powSq (b * b) (e / 2)
    if e % 2 = 0 then h else b * h
termination_by e
decreasing_by omega

theorem powSq_eq (b e : Nat) : powSq b e = b ^ e := by
  induction e using Nat.strongRecOn generalizing b with
  | _ e ih =>
    rw [powSq.eq_def]
    split
    · subst_vars; rfl
    · rename_i he
      simp only
      rw [ih (e / 2) (by omega) (b * b)]
      have hsq : (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) := by rw [Nat.pow_mul, Nat.pow_two]
      split
      · rename_i h2; rw [hsq]; congr 1; omega
      · rename_i h2
        rw [hsq, ← Nat.pow_succ']; congr 1; omega

/-- `Nat.pow`, with the powers of two of fixed-width types as literals. -/
def natPow (b e : Nat) : Nat :=
  if b = 2 then
    if e = 64 then two64 else if e = 32 then 4294967296 else if e = 8 then 256 else powSq 2 e
  else powSq b e

theorem natPow_eq (b e : Nat) : Nat.pow b e = natPow b e := by
  show b ^ e = natPow b e
  unfold natPow
  split
  · subst_vars
    split
    · subst_vars; rfl
    split
    · subst_vars; rfl
    split
    · subst_vars; rfl
    exact (powSq_eq 2 e).symm
  · exact (powSq_eq b e).symm

/-- `Nat.shiftLeft` through the fast power. -/
def natShiftLeft (a n : Nat) : Nat := a * natPow 2 n
/-- `Nat.shiftRight` through the fast power. -/
def natShiftRight (a n : Nat) : Nat := a / natPow 2 n

theorem natShiftLeft_eq (a n : Nat) : Nat.shiftLeft a n = natShiftLeft a n := by
  rw [natShiftLeft, ← natPow_eq]; exact Nat.shiftLeft_eq a n

theorem natShiftRight_eq (a n : Nat) : Nat.shiftRight a n = natShiftRight a n := by
  rw [natShiftRight, ← natPow_eq]; exact Nat.shiftRight_eq_div_pow a n

end ConPastel.Impl

cake_replace Nat.xor ConPastel.Impl.natXor ConPastel.Impl.natXor_eq
cake_replace Nat.land ConPastel.Impl.natLand ConPastel.Impl.natLand_eq
cake_replace Nat.lor ConPastel.Impl.natLor ConPastel.Impl.natLor_eq
cake_replace Nat.pow ConPastel.Impl.natPow ConPastel.Impl.natPow_eq
cake_replace Nat.shiftLeft ConPastel.Impl.natShiftLeft ConPastel.Impl.natShiftLeft_eq
cake_replace Nat.shiftRight ConPastel.Impl.natShiftRight ConPastel.Impl.natShiftRight_eq
