import ConPastel.Translator.Word
import ConPastel.Translator.EqType

/-!
# `UInt64` as CakeML 64-bit words

A `UInt64` is represented by a CakeML `Word64` (`UINT64`), not by the `Nat`
inside its `BitVec`: hashes and packed data words then live in one machine
word instead of a bignum, and the operations are machine instructions instead
of bignum arithmetic followed by a reduction modulo `2 ^ 64`.

CakeML has native word addition, subtraction and bitwise operations, and
shifts by a constant amount. Multiplication, division and remainder go
through integers; a shift by a variable amount is a barrel shifter of
constant shifts (`shlB`, `shrB`).
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString

/-! ## Word lemmas -/

theorem Eval_w64_add {env : SemEnv Value} {e₁ e₂ : Exp} {a b : BitVec 64}
    (h₁ : Eval env e₁ (W64 a)) (h₂ : Eval env e₂ (W64 b)) :
    Eval env (.app (.arith .add (.wordT .w64)) [e₁, e₂]) (W64 (a + b)) :=
  Eval_binop rfl h₁ h₂ fun v₁ v₂ p₁ p₂ => by
    subst p₁ p₂
    exact ⟨_, rfl, fun refs ffi => by simp [doApp_arith_core, doAppNumericCore, wordArith]⟩

theorem Eval_w64_sub {env : SemEnv Value} {e₁ e₂ : Exp} {a b : BitVec 64}
    (h₁ : Eval env e₁ (W64 a)) (h₂ : Eval env e₂ (W64 b)) :
    Eval env (.app (.arith .sub (.wordT .w64)) [e₁, e₂]) (W64 (a - b)) :=
  Eval_binop rfl h₁ h₂ fun v₁ v₂ p₁ p₂ => by
    subst p₁ p₂
    exact ⟨_, rfl, fun refs ffi => by simp [doApp_arith_core, doAppNumericCore, wordArith]⟩

theorem Eval_w64_shl {env : SemEnv Value} {e : Exp} {a : BitVec 64} (k : Nat)
    (h : Eval env e (W64 a)) :
    Eval env (.app (.shift .w64 .lsl k) [e]) (W64 (a <<< k)) :=
  Eval_unop rfl h fun v hv => by
    subst hv
    exact ⟨_, rfl, fun refs ffi => by simp [doApp, doAppBasic, doAppNumericCore, shift64Lookup]⟩

theorem Eval_w64_shr {env : SemEnv Value} {e : Exp} {a : BitVec 64} (k : Nat)
    (h : Eval env e (W64 a)) :
    Eval env (.app (.shift .w64 .lsr k) [e]) (W64 (a >>> k)) :=
  Eval_unop rfl h fun v hv => by
    subst hv
    exact ⟨_, rfl, fun refs ffi => by simp [doApp, doAppBasic, doAppNumericCore, shift64Lookup]⟩

/-! ## Certificates of primitives over any invariants -/

theorem prim_lookup_p1 (envC : SemEnv Value) (funs : List (VarN × VarN × Exp)) (xv : Value) :
    nsLookup (recBodyEnv envC funs (ofString "p") xv).v (.short (ofString "p")) = some xv := by
  simp +decide [recBodyEnv, nsLookup_nsBind_short]

theorem prim1g_cert {α β : Type} {A : RefInv α} {B : RefInv β} {f : α → β} {body : Exp}
    (envC : SemEnv Value) (funs : List (VarN × VarN × Exp)) (n : VarN)
    (hnodup : (funs.map fun (f, _, _) => f).Nodup)
    (hfind : findRecFun n funs = some (ofString "p", body))
    (h : ∀ x xv, A x xv → Eval (recBodyEnv envC funs (ofString "p") xv) (V "p") (A x) →
      Eval (recBodyEnv envC funs (ofString "p") xv) body (B (f x))) :
    Arrow A B f (.recclosure envC funs n) := by
  intro x xv hx
  exact AppReturns_recclosure hnodup hfind
    (h x xv hx (Eval_var _ _ xv _ (prim_lookup_p1 envC funs xv) hx))

theorem prim2g_cert {α γ β : Type} {A : RefInv α} {C : RefInv γ} {B : RefInv β} {f : α → γ → β}
    {body : Exp} (envC : SemEnv Value) (funs : List (VarN × VarN × Exp)) (n : VarN)
    (hnodup : (funs.map fun (f, _, _) => f).Nodup)
    (hfind : findRecFun n funs = some (ofString "p", .fn (ofString "b") body))
    (h : ∀ x xv y yv,
      Eval (SemEnv.mk (nsBind (ofString "b") yv (recBodyEnv envC funs (ofString "p") xv).v)
        (recBodyEnv envC funs (ofString "p") xv).c) (V "p") (A x) →
      Eval (SemEnv.mk (nsBind (ofString "b") yv (recBodyEnv envC funs (ofString "p") xv).v)
        (recBodyEnv envC funs (ofString "p") xv).c) (V "b") (C y) →
      Eval (SemEnv.mk (nsBind (ofString "b") yv (recBodyEnv envC funs (ofString "p") xv).v)
        (recBodyEnv envC funs (ofString "p") xv).c) body (B (f x y))) :
    Arrow A (Arrow C B) f (.recclosure envC funs n) := by
  intro x xv hx
  apply AppReturns_recclosure hnodup hfind
  apply Eval_fn_arrow
  intro y yv hy
  exact h x xv y yv (Eval_var _ _ xv _ (prim_lookup_p envC funs xv yv) hx)
    (Eval_var _ _ yv _ (prim_lookup_b envC funs xv yv) hy)

/-- A `UINT64` value is a `W64` of its bits. -/
theorem Eval_u64_w {env : SemEnv Value} {e : Exp} {x : UInt64} (h : Eval env e (UINT64 x)) :
    Eval env e (W64 x.toBitVec) := h

theorem Eval_w_u64 {env : SemEnv Value} {e : Exp} {x : UInt64} {w : BitVec 64}
    (h : Eval env e (W64 w)) (hw : w = x.toBitVec) : Eval env e (UINT64 x) := by
  subst hw; exact h

/-- The body of a native binary word primitive. -/
def w64Body (op : Arith) : Exp := .fn (ofString "b") (.app (.arith op (.wordT .w64)) [V "p", V "b"])

/-- `w2i e`. -/
def w2i (e : Exp) : Exp := .app (.fromTo (.wordT .w64) .intT) [e]
/-- `i2w e`. -/
def i2w (e : Exp) : Exp := .app (.fromTo .intT (.wordT .w64)) [e]

end ConPastel.Translator

namespace ConPastel.Impl

/-! ## Constant shifts -/

def shl1 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 1⟩
def shl2 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 2⟩
def shl4 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 4⟩
def shl8 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 8⟩
def shl16 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 16⟩
def shl32 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 32⟩
def shr1 (a : UInt64) : UInt64 := ⟨a.toBitVec >>> 1⟩
def shr2 (a : UInt64) : UInt64 := ⟨a.toBitVec >>> 2⟩
def shr4 (a : UInt64) : UInt64 := ⟨a.toBitVec >>> 4⟩
def shr8 (a : UInt64) : UInt64 := ⟨a.toBitVec >>> 8⟩
def shr16 (a : UInt64) : UInt64 := ⟨a.toBitVec >>> 16⟩
def shr32 (a : UInt64) : UInt64 := ⟨a.toBitVec >>> 32⟩
def shr47 (a : UInt64) : UInt64 := ⟨a.toBitVec >>> 47⟩
def shl33 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 33⟩
def shl24 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 24⟩
def shl40 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 40⟩
def shl56 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 56⟩
def shl48 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 48⟩
def shl63 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 63⟩
def shr49 (a : UInt64) : UInt64 := ⟨a.toBitVec >>> 49⟩
def shr63 (a : UInt64) : UInt64 := ⟨a.toBitVec >>> 63⟩

def sl32 (k : Nat) (a : UInt64) : UInt64 := if k / 32 % 2 = 1 then shl32 a else a
def sl16 (k : Nat) (a : UInt64) : UInt64 := if k / 16 % 2 = 1 then shl16 a else a
def sl8 (k : Nat) (a : UInt64) : UInt64 := if k / 8 % 2 = 1 then shl8 a else a
def sl4 (k : Nat) (a : UInt64) : UInt64 := if k / 4 % 2 = 1 then shl4 a else a
def sl2 (k : Nat) (a : UInt64) : UInt64 := if k / 2 % 2 = 1 then shl2 a else a
def sl1 (k : Nat) (a : UInt64) : UInt64 := if k % 2 = 1 then shl1 a else a
def sr32 (k : Nat) (a : UInt64) : UInt64 := if k / 32 % 2 = 1 then shr32 a else a
def sr16 (k : Nat) (a : UInt64) : UInt64 := if k / 16 % 2 = 1 then shr16 a else a
def sr8 (k : Nat) (a : UInt64) : UInt64 := if k / 8 % 2 = 1 then shr8 a else a
def sr4 (k : Nat) (a : UInt64) : UInt64 := if k / 4 % 2 = 1 then shr4 a else a
def sr2 (k : Nat) (a : UInt64) : UInt64 := if k / 2 % 2 = 1 then shr2 a else a
def sr1 (k : Nat) (a : UInt64) : UInt64 := if k % 2 = 1 then shr1 a else a

/-- `a <<< k` for `k < 64`: six conditional constant shifts. -/
def shlB (a : UInt64) (k : Nat) : UInt64 := sl1 k (sl2 k (sl4 k (sl8 k (sl16 k (sl32 k a)))))
/-- `a >>> k` for `k < 64`. -/
def shrB (a : UInt64) (k : Nat) : UInt64 := sr1 k (sr2 k (sr4 k (sr8 k (sr16 k (sr32 k a)))))

theorem ushiftRight_add' (x : BitVec 64) (n m : Nat) : x >>> n >>> m = x >>> (n + m) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.pow_add]

section
variable (k : Nat) (a : UInt64)
theorem sl32_bv : (sl32 k a).toBitVec = a.toBitVec <<< (if k / 32 % 2 = 1 then 32 else 0) := by
  unfold sl32 shl32; split <;> simp
theorem sl16_bv : (sl16 k a).toBitVec = a.toBitVec <<< (if k / 16 % 2 = 1 then 16 else 0) := by
  unfold sl16 shl16; split <;> simp
theorem sl8_bv : (sl8 k a).toBitVec = a.toBitVec <<< (if k / 8 % 2 = 1 then 8 else 0) := by
  unfold sl8 shl8; split <;> simp
theorem sl4_bv : (sl4 k a).toBitVec = a.toBitVec <<< (if k / 4 % 2 = 1 then 4 else 0) := by
  unfold sl4 shl4; split <;> simp
theorem sl2_bv : (sl2 k a).toBitVec = a.toBitVec <<< (if k / 2 % 2 = 1 then 2 else 0) := by
  unfold sl2 shl2; split <;> simp
theorem sl1_bv : (sl1 k a).toBitVec = a.toBitVec <<< (if k % 2 = 1 then 1 else 0) := by
  unfold sl1 shl1; split <;> simp
theorem sr32_bv : (sr32 k a).toBitVec = a.toBitVec >>> (if k / 32 % 2 = 1 then 32 else 0) := by
  unfold sr32 shr32; split <;> simp
theorem sr16_bv : (sr16 k a).toBitVec = a.toBitVec >>> (if k / 16 % 2 = 1 then 16 else 0) := by
  unfold sr16 shr16; split <;> simp
theorem sr8_bv : (sr8 k a).toBitVec = a.toBitVec >>> (if k / 8 % 2 = 1 then 8 else 0) := by
  unfold sr8 shr8; split <;> simp
theorem sr4_bv : (sr4 k a).toBitVec = a.toBitVec >>> (if k / 4 % 2 = 1 then 4 else 0) := by
  unfold sr4 shr4; split <;> simp
theorem sr2_bv : (sr2 k a).toBitVec = a.toBitVec >>> (if k / 2 % 2 = 1 then 2 else 0) := by
  unfold sr2 shr2; split <;> simp
theorem sr1_bv : (sr1 k a).toBitVec = a.toBitVec >>> (if k % 2 = 1 then 1 else 0) := by
  unfold sr1 shr1; split <;> simp
end

theorem bits64 : ∀ k : Nat, k < 64 →
    (if k / 32 % 2 = 1 then 32 else 0) + (if k / 16 % 2 = 1 then 16 else 0) +
      (if k / 8 % 2 = 1 then 8 else 0) + (if k / 4 % 2 = 1 then 4 else 0) +
      (if k / 2 % 2 = 1 then 2 else 0) + (if k % 2 = 1 then 1 else 0) = k := by
  decide

theorem shlB_eq (a : UInt64) (k : Nat) (hk : k < 64) : shlB a k = ⟨a.toBitVec <<< k⟩ := by
  apply UInt64.toBitVec_inj.mp
  rw [shlB, sl1_bv, sl2_bv, sl4_bv, sl8_bv, sl16_bv, sl32_bv]
  simp only [← BitVec.shiftLeft_add]
  rw [bits64 k hk]

theorem shrB_eq (a : UInt64) (k : Nat) (hk : k < 64) : shrB a k = ⟨a.toBitVec >>> k⟩ := by
  apply UInt64.toBitVec_inj.mp
  rw [shrB, sr1_bv, sr2_bv, sr4_bv, sr8_bv, sr16_bv, sr32_bv]
  simp only [ushiftRight_add']
  rw [bits64 k hk]

/-- `UInt64.shiftLeft`: the amount modulo 64, then the barrel shifter. -/
def shiftLeftW (a b : UInt64) : UInt64 := shlB a (b.toNat % 64)
/-- `UInt64.shiftRight`: the amount modulo 64, then the barrel shifter. -/
def shiftRightW (a b : UInt64) : UInt64 := shrB a (b.toNat % 64)

theorem shiftLeft_eq_B (a b : UInt64) : a.shiftLeft b = shiftLeftW a b := by
  unfold shiftLeftW
  rw [shlB_eq a _ (Nat.mod_lt _ (by decide))]
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.shiftLeft, BitVec.shiftLeft_eq']
  rw [show b.mod 64 = b % 64 from rfl]
  congr 1

theorem shiftRight_eq_B (a b : UInt64) : a.shiftRight b = shiftRightW a b := by
  unfold shiftRightW
  rw [shrB_eq a _ (Nat.mod_lt _ (by decide))]
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.shiftRight, BitVec.ushiftRight_eq']
  rw [show b.mod 64 = b % 64 from rfl]
  congr 1

/-! ## Equality, conversions -/

/-- CakeML's `=` on words. -/
def u64EqB (a b : UInt64) : Bool := decide (a = b)

/-- `UInt64.decEq` through CakeML's `=` on words. -/
def u64DecEq (a b : UInt64) : Decidable (a = b) :=
  if h : u64EqB a b = true then isTrue (of_decide_eq_true h)
  else isFalse (fun e => h (by subst e; exact decide_eq_true rfl))

theorem u64_decEq_eq (a b : UInt64) : UInt64.decEq a b = u64DecEq a b := Subsingleton.elim _ _

/-- `UInt64.toBitVec` from the word's value. -/
/- `BitVec.ofNatLT`, not `BitVec.ofNat`: no reduction modulo `2 ^ 64` (a bignum),
so a `UInt64` comparison is a word-to-integer conversion and an integer test. -/
def u64toBV (a : UInt64) : BitVec 64 := BitVec.ofNatLT a.toNat a.toNat_lt

theorem u64_toBitVec_eq (a : UInt64) : a.toBitVec = u64toBV a := by
  apply BitVec.eq_of_toNat_eq; simp [u64toBV]

/-- `UInt8.toUInt64` through `UInt64.ofNat`. -/
def u8toU64 (a : UInt8) : UInt64 := UInt64.ofNat a.toNat

theorem u8_toUInt64_eq (a : UInt8) : a.toUInt64 = u8toU64 a := by
  unfold u8toU64
  apply UInt64.toNat_inj.mp
  show (UInt8.toUInt64 a).toNat = (BitVec.ofNat 64 a.toNat).toNat
  rw [BitVec.toNat_ofNat, UInt8.toNat_toUInt64]
  exact (Nat.mod_eq_of_lt (Nat.lt_trans a.toNat_lt (by decide))).symm

end ConPastel.Impl

/-! ## The primitives -/

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString

cake_primitive UInt64.add (w64Body .add) by
  intro envC funs hnodup hfind _ _ _
  refine prim2g_cert envC funs _ hnodup hfind fun x xv y yv ha hb => ?_
  exact Eval_w_u64 (Eval_w64_add (Eval_u64_w ha) (Eval_u64_w hb)) rfl

cake_primitive UInt64.sub (w64Body .sub) by
  intro envC funs hnodup hfind _ _ _
  refine prim2g_cert envC funs _ hnodup hfind fun x xv y yv ha hb => ?_
  exact Eval_w_u64 (Eval_w64_sub (Eval_u64_w ha) (Eval_u64_w hb)) rfl

cake_primitive UInt64.xor (w64Body .xor) by
  intro envC funs hnodup hfind _ _ _
  refine prim2g_cert envC funs _ hnodup hfind fun x xv y yv ha hb => ?_
  exact Eval_w_u64 (Eval_w64_xor (Eval_u64_w ha) (Eval_u64_w hb)) rfl

cake_primitive UInt64.land (w64Body .and) by
  intro envC funs hnodup hfind _ _ _
  refine prim2g_cert envC funs _ hnodup hfind fun x xv y yv ha hb => ?_
  exact Eval_w_u64 (Eval_w64_and (Eval_u64_w ha) (Eval_u64_w hb)) rfl

cake_primitive UInt64.lor (w64Body .or) by
  intro envC funs hnodup hfind _ _ _
  refine prim2g_cert envC funs _ hnodup hfind fun x xv y yv ha hb => ?_
  exact Eval_w_u64 (Eval_w64_or (Eval_u64_w ha) (Eval_u64_w hb)) rfl

cake_primitive UInt64.mul
  (Exp.fn (ofString "b") (i2w (.app (.arith .mul .intT) [w2i (V "p"), w2i (V "b")]))) by
  intro envC funs hnodup hfind _ _ _
  refine prim2g_cert envC funs _ hnodup hfind fun x xv y yv ha hb => ?_
  refine Eval_w_u64 (Eval_int_to_w64 (Eval_int_mul (Eval_w64_to_int (Eval_u64_w ha))
    (Eval_w64_to_int (Eval_u64_w hb)))) ?_
  show BitVec.ofInt 64 (↑(x.toBitVec.toNat) * ↑(y.toBitVec.toNat)) = x.toBitVec * y.toBitVec
  rw [← Int.natCast_mul, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]

cake_primitive UInt64.toNat (w2i (V "p")) by
  intro envC funs hnodup hfind _ _ _
  refine prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => ?_
  exact Eval_weaken (Eval_w64_to_int (Eval_u64_w ha)) fun w hw => by
    simp only [INT] at hw; simp [NAT, hw]

cake_primitive UInt64.ofNat (i2w (V "p")) by
  intro envC funs hnodup hfind _ _ _
  refine prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => ?_
  exact Eval_w_u64 (Eval_int_to_w64 ha) (by simp [UInt64.ofNat, BitVec.ofInt_natCast])

cake_primitive ConPastel.Impl.u64EqB (Exp.fn (ofString "b") (.app .equality [V "p", V "b"])) by
  intro envC funs hnodup hfind _ _ _
  exact primEq_cert eqType_UINT64 (fun x y => by simp [ConPastel.Impl.u64EqB]) envC funs _ hnodup hfind

cake_primitive UInt64.div
  (Exp.fn (ofString "b") (.if_ (.app .equality [w2i (V "b"), .lit (.intLit 0)]) (.lit (.word64 0))
    (i2w (.app (.arith .div .intT) [w2i (V "p"), w2i (V "b")])))) by
  intro envC funs hnodup hfind _ _ _
  refine prim2g_cert envC funs _ hnodup hfind fun x xv y yv ha hb => ?_
  have hbi := Eval_w64_to_int (Eval_u64_w hb)
  have hai := Eval_w64_to_int (Eval_u64_w ha)
  refine Eval_if (Eval_int_eq hbi (Eval_lit _ (.intLit 0) (INT 0) rfl)) (fun h => ?_) (fun h => ?_)
  · have hy : y = 0 := UInt64.toNat_inj.mp (by simpa using h)
    subst hy
    exact Eval_lit _ _ _ (by
      show _ = Value.litv (.word64 (x.toBitVec.udiv (0 : UInt64).toBitVec)); simp)
  · have h0 : y.toBitVec.toNat ≠ 0 := by simpa using h
    refine Eval_w_u64 (Eval_int_to_w64 (Eval_int_div (by exact_mod_cast h0) hai hbi)) ?_
    have hfd : ((x.toBitVec.toNat : Int)).fdiv (y.toBitVec.toNat : Int) =
        ((x.toBitVec.toNat / y.toBitVec.toNat : Nat) : Int) := by
      rw [Int.fdiv_eq_ediv]; simp
    rw [hfd, BitVec.ofInt_natCast]
    show _ = x.toBitVec.udiv y.toBitVec
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_udiv]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.toNat_lt

cake_primitive UInt64.mod
  (Exp.fn (ofString "b") (.if_ (.app .equality [w2i (V "b"), .lit (.intLit 0)]) (V "p")
    (i2w (.app (.arith .mod .intT) [w2i (V "p"), w2i (V "b")])))) by
  intro envC funs hnodup hfind _ _ _
  refine prim2g_cert envC funs _ hnodup hfind fun x xv y yv ha hb => ?_
  have hbi := Eval_w64_to_int (Eval_u64_w hb)
  have hai := Eval_w64_to_int (Eval_u64_w ha)
  refine Eval_if (Eval_int_eq hbi (Eval_lit _ (.intLit 0) (INT 0) rfl)) (fun h => ?_) (fun h => ?_)
  · have hy : y = 0 := UInt64.toNat_inj.mp (by simpa using h)
    subst hy
    exact Eval_w_u64 (Eval_u64_w ha) (by
      show x.toBitVec = x.toBitVec.umod (0 : UInt64).toBitVec; simp)
  · have h0 : y.toBitVec.toNat ≠ 0 := by simpa using h
    refine Eval_w_u64 (Eval_int_to_w64 (Eval_int_mod (by exact_mod_cast h0) hai hbi)) ?_
    have hfm : ((x.toBitVec.toNat : Int)).fmod (y.toBitVec.toNat : Int) =
        ((x.toBitVec.toNat % y.toBitVec.toNat : Nat) : Int) := by
      rw [Int.fmod_eq_emod]; simp
    rw [hfm, BitVec.ofInt_natCast]
    show _ = x.toBitVec.umod y.toBitVec
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_umod]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.toNat_lt

cake_primitive ConPastel.Impl.shl1 (.app (.shift .w64 .lsl 1) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 1 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shl2 (.app (.shift .w64 .lsl 2) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 2 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shl4 (.app (.shift .w64 .lsl 4) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 4 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shl8 (.app (.shift .w64 .lsl 8) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 8 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shl16 (.app (.shift .w64 .lsl 16) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 16 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shl32 (.app (.shift .w64 .lsl 32) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 32 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shr1 (.app (.shift .w64 .lsr 1) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shr 1 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shr2 (.app (.shift .w64 .lsr 2) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shr 2 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shr4 (.app (.shift .w64 .lsr 4) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shr 4 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shr8 (.app (.shift .w64 .lsr 8) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shr 8 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shr16 (.app (.shift .w64 .lsr 16) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shr 16 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shr32 (.app (.shift .w64 .lsr 32) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shr 32 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shl33 (.app (.shift .w64 .lsl 33) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 33 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shl48 (.app (.shift .w64 .lsl 48) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 48 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shl63 (.app (.shift .w64 .lsl 63) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 63 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shr49 (.app (.shift .w64 .lsr 49) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shr 49 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shr63 (.app (.shift .w64 .lsr 63) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shr 63 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shl24 (.app (.shift .w64 .lsl 24) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 24 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shl40 (.app (.shift .w64 .lsl 40) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 40 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shl56 (.app (.shift .w64 .lsl 56) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 56 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shr47 (.app (.shift .w64 .lsr 47) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shr 47 (Eval_u64_w ha)) rfl

cake_replace UInt64.shiftLeft ConPastel.Impl.shiftLeftW ConPastel.Impl.shiftLeft_eq_B
cake_replace UInt64.decEq ConPastel.Impl.u64DecEq ConPastel.Impl.u64_decEq_eq
cake_replace UInt64.toBitVec ConPastel.Impl.u64toBV ConPastel.Impl.u64_toBitVec_eq
cake_replace UInt8.toUInt64 ConPastel.Impl.u8toU64 ConPastel.Impl.u8_toUInt64_eq

/-! ## Fast paths: constant shift amounts, and the powers of two of con-leche's data words

`scrambleHash` shifts by 32 and 16; con-leche packs and reads its data words
with multiplication, division and remainder by powers of two, which on
integers are bignum operations for words above `2 ^ 62`. Each is checked for
first and done as a native shift or mask; otherwise the operation runs as
before (an unreplaced copy of the primitive). -/

namespace ConPastel.Impl

theorem u64EqB_true {a b : UInt64} (h : u64EqB a b = true) : a = b := of_decide_eq_true h

/-- `UInt64.shiftRight`, the amounts `mixHash` and `scrambleHash` use as one native shift. -/
def shiftRightF (a b : UInt64) : UInt64 :=
  if u64EqB b 47 then shr47 a else if u64EqB b 32 then shr32 a else if u64EqB b 16 then shr16 a else shiftRightW a b

theorem shiftRight_eq_F (a b : UInt64) : a.shiftRight b = shiftRightF a b := by
  unfold shiftRightF
  split
  · rename_i h; cases u64EqB_true h
    apply UInt64.toBitVec_inj.mp; simp [shr47, UInt64.shiftRight]; rfl
  split
  · rename_i h; cases u64EqB_true h
    apply UInt64.toBitVec_inj.mp; simp [shr32, UInt64.shiftRight]; rfl
  split
  · rename_i h; cases u64EqB_true h
    apply UInt64.toBitVec_inj.mp; simp [shr16, UInt64.shiftRight]; rfl
  · exact shiftRight_eq_B a b

theorem pow2_mul_eq (a : UInt64) (k : Nat) (hk : k < 64) : (⟨a.toBitVec <<< k⟩ : UInt64) = a * UInt64.ofNat (2 ^ k) := by
  apply UInt64.toNat_inj.mp
  show (a.toBitVec <<< k).toNat = (a * UInt64.ofNat (2 ^ k)).toNat
  rw [BitVec.toNat_shiftLeft, UInt64.toNat_mul, UInt64.toNat_ofNat', Nat.shiftLeft_eq]
  have : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  rw [Nat.mod_eq_of_lt this]; rfl

theorem pow2_div_eq (a : UInt64) (k : Nat) (hk : k < 64) : (⟨a.toBitVec >>> k⟩ : UInt64) = a / UInt64.ofNat (2 ^ k) := by
  apply UInt64.toNat_inj.mp
  show (a.toBitVec >>> k).toNat = (a / UInt64.ofNat (2 ^ k)).toNat
  rw [BitVec.toNat_ushiftRight, UInt64.toNat_div, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  have : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  rw [Nat.mod_eq_of_lt this]; rfl

theorem pow2_mod_eq (a : UInt64) (k : Nat) (hk : k < 64) : a &&& UInt64.ofNat (2 ^ k - 1) = a % UInt64.ofNat (2 ^ k) := by
  apply UInt64.toNat_inj.mp
  have : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  rw [UInt64.toNat_and, UInt64.toNat_mod, UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt this,
    Nat.mod_eq_of_lt (by omega), Nat.and_two_pow_sub_one_eq_mod]

/-- Unreplaced copies of the arithmetic primitives (the fallbacks below). -/
def u64mulP (a b : UInt64) : UInt64 := a * b
def u64divP (a b : UInt64) : UInt64 := a / b
def u64modP (a b : UInt64) : UInt64 := a % b

/-! Multiplication of words without bignums: CakeML has no word
multiplication, and the product of two words as integers is a bignum. On
22-bit limbs every partial product is a small integer. -/

def shr22 (a : UInt64) : UInt64 := ⟨a.toBitVec >>> 22⟩
def shr44 (a : UInt64) : UInt64 := ⟨a.toBitVec >>> 44⟩
def shl22 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 22⟩
def shl44 (a : UInt64) : UInt64 := ⟨a.toBitVec <<< 44⟩

/-- Multiplication on 22-bit limbs: the limb products stay small integers. -/
def mulL (a b : UInt64) : UInt64 :=
  let a0 := (a &&& 4194303).toNat
  let a1 := (shr22 a &&& 4194303).toNat
  let a2 := (shr44 a).toNat
  let b0 := (b &&& 4194303).toNat
  let b1 := (shr22 b &&& 4194303).toNat
  let b2 := (shr44 b).toNat
  UInt64.ofNat (a0 * b0) + shl22 (UInt64.ofNat (a0 * b1 + a1 * b0)) +
    shl44 (UInt64.ofNat (a0 * b2 + a1 * b1 + a2 * b0))

theorem ring3 (K a0 a1 a2 b0 b1 b2 : Nat) : (a0 + K * a1 + K * K * a2) * (b0 + K * b1 + K * K * b2) =
    (a0 * b0 + (a0 * b1 + a1 * b0) * K + (a0 * b2 + a1 * b1 + a2 * b0) * (K * K))
      + K * K * K * ((a1 * b2 + a2 * b1) + K * (a2 * b2)) := by
  grind

theorem nat_limbs (A B : Nat) :
    (A % 2^22 * (B % 2^22) + (A % 2^22 * (B / 2^22 % 2^22) + A / 2^22 % 2^22 * (B % 2^22)) * 2^22
      + (A % 2^22 * (B / 2^44) + A / 2^22 % 2^22 * (B / 2^22 % 2^22) + A / 2^44 * (B % 2^22)) * 2^44) % 2^64
    = A * B % 2^64 := by
  have hA : A = A % 2^22 + 2^22 * (A / 2^22 % 2^22) + 2^22 * 2^22 * (A / 2^44) := by omega
  have hB : B = B % 2^22 + 2^22 * (B / 2^22 % 2^22) + 2^22 * 2^22 * (B / 2^44) := by omega
  generalize A % 2^22 = a0, A / 2^22 % 2^22 = a1, A / 2^44 = a2 at hA ⊢
  generalize B % 2^22 = b0, B / 2^22 % 2^22 = b1, B / 2^44 = b2 at hB ⊢
  subst hA hB
  rw [ring3, show (2:Nat)^22 * 2^22 * 2^22 = 2^64 * 4 by decide, show (2:Nat)^22 * 2^22 = 2^44 by decide,
    Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem mulL_eq (a b : UInt64) : u64mulP a b = mulL a b := by
  apply UInt64.toNat_inj.mp
  unfold u64mulP
  have h1 : (4194303 : UInt64).toNat = 2^22 - 1 := rfl
  have e22 : ∀ x : UInt64, (shr22 x).toNat = x.toNat / 2^22 := fun x => by
    show (x.toBitVec >>> 22).toNat = _; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have e44 : ∀ x : UInt64, (shr44 x).toNat = x.toNat / 2^44 := fun x => by
    show (x.toBitVec >>> 44).toNat = _; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have s22 : ∀ x : UInt64, (shl22 x).toNat = x.toNat * 2^22 % 2^64 := fun x => by
    show (x.toBitVec <<< 22).toNat = _; rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; rfl
  have s44 : ∀ x : UInt64, (shl44 x).toNat = x.toNat * 2^44 % 2^64 := fun x => by
    show (x.toBitVec <<< 44).toNat = _; rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; rfl
  simp only [mulL, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_and, UInt64.toNat_ofNat', h1, e22, e44,
    s22, s44, Nat.and_two_pow_sub_one_eq_mod]
  rw [← nat_limbs a.toNat b.toNat]
  simp only [Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod]
/-- Multiplication: by the powers of two con-leche packs data words with, a shift. -/
def mulF (a b : UInt64) : UInt64 :=
  if u64EqB b 2 then shl1 a else if u64EqB b 65536 then shl16 a
  else if u64EqB b 4294967296 then shl32 a else mulL a b

/-- Division: by those powers of two, a shift. -/
def divF (a b : UInt64) : UInt64 :=
  if u64EqB b 2 then shr1 a else if u64EqB b 65536 then shr16 a
  else if u64EqB b 4294967296 then shr32 a else u64divP a b

/-- Remainder: by the powers of two con-leche reads fields with, a mask. -/
def modF (a b : UInt64) : UInt64 :=
  if u64EqB b 2 then a &&& 1 else if u64EqB b 32768 then a &&& 32767
  else if u64EqB b 4294967296 then a &&& 4294967295 else u64modP a b

theorem mul_eq_F (a b : UInt64) : UInt64.mul a b = mulF a b := by
  unfold mulF
  split
  · rename_i h; cases u64EqB_true h
    exact (pow2_mul_eq a 1 (by decide)).symm
  split
  · rename_i h; cases u64EqB_true h
    exact (pow2_mul_eq a 16 (by decide)).symm
  split
  · rename_i h; cases u64EqB_true h
    exact (pow2_mul_eq a 32 (by decide)).symm
  · exact mulL_eq a b

theorem div_eq_F (a b : UInt64) : UInt64.div a b = divF a b := by
  unfold divF
  split
  · rename_i h; cases u64EqB_true h
    exact (pow2_div_eq a 1 (by decide)).symm
  split
  · rename_i h; cases u64EqB_true h
    exact (pow2_div_eq a 16 (by decide)).symm
  split
  · rename_i h; cases u64EqB_true h
    exact (pow2_div_eq a 32 (by decide)).symm
  · rfl

theorem mod_eq_F (a b : UInt64) : UInt64.mod a b = modF a b := by
  unfold modF
  split
  · rename_i h; cases u64EqB_true h
    exact (pow2_mod_eq a 1 (by decide)).symm
  split
  · rename_i h; cases u64EqB_true h
    exact (pow2_mod_eq a 15 (by decide)).symm
  split
  · rename_i h; cases u64EqB_true h
    exact (pow2_mod_eq a 32 (by decide)).symm
  · rfl

/-- `DecidableEq UInt64` as CakeML's `=` (the instance is passed unapplied, e.g. to `bne`). -/
def u64DecEqI : DecidableEq UInt64 := fun a b => u64DecEq a b

theorem instDecidableEqUInt64_eq : instDecidableEqUInt64 = u64DecEqI :=
  funext fun _ => funext fun _ => Subsingleton.elim _ _

end ConPastel.Impl

cake_primitive ConPastel.Impl.shr22 (.app (.shift .w64 .lsr 22) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shr 22 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shr44 (.app (.shift .w64 .lsr 44) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shr 44 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shl22 (.app (.shift .w64 .lsl 22) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 22 (Eval_u64_w ha)) rfl
cake_primitive ConPastel.Impl.shl44 (.app (.shift .w64 .lsl 44) [V "p"]) by
  intro envC funs hnodup hfind _ _ _
  exact prim1g_cert envC funs _ hnodup hfind fun x xv _ ha => Eval_w_u64 (Eval_w64_shl 44 (Eval_u64_w ha)) rfl

cake_primitive ConPastel.Impl.u64mulP
  (Exp.fn (ofString "b") (i2w (.app (.arith .mul .intT) [w2i (V "p"), w2i (V "b")]))) by
  intro envC funs hnodup hfind _ _ _
  refine prim2g_cert envC funs _ hnodup hfind fun x xv y yv ha hb => ?_
  refine Eval_w_u64 (Eval_int_to_w64 (Eval_int_mul (Eval_w64_to_int (Eval_u64_w ha))
    (Eval_w64_to_int (Eval_u64_w hb)))) ?_
  show BitVec.ofInt 64 (↑(x.toBitVec.toNat) * ↑(y.toBitVec.toNat)) = x.toBitVec * y.toBitVec
  rw [← Int.natCast_mul, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]

cake_primitive ConPastel.Impl.u64divP
  (Exp.fn (ofString "b") (.if_ (.app .equality [w2i (V "b"), .lit (.intLit 0)]) (.lit (.word64 0))
    (i2w (.app (.arith .div .intT) [w2i (V "p"), w2i (V "b")])))) by
  intro envC funs hnodup hfind _ _ _
  refine prim2g_cert envC funs _ hnodup hfind fun x xv y yv ha hb => ?_
  have hbi := Eval_w64_to_int (Eval_u64_w hb)
  have hai := Eval_w64_to_int (Eval_u64_w ha)
  refine Eval_if (Eval_int_eq hbi (Eval_lit _ (.intLit 0) (INT 0) rfl)) (fun h => ?_) (fun h => ?_)
  · have hy : y = 0 := UInt64.toNat_inj.mp (by simpa using h)
    subst hy
    exact Eval_lit _ _ _ (by
      show _ = Value.litv (.word64 (x.toBitVec.udiv (0 : UInt64).toBitVec)); simp)
  · have h0 : y.toBitVec.toNat ≠ 0 := by simpa using h
    refine Eval_w_u64 (Eval_int_to_w64 (Eval_int_div (by exact_mod_cast h0) hai hbi)) ?_
    have hfd : ((x.toBitVec.toNat : Int)).fdiv (y.toBitVec.toNat : Int) =
        ((x.toBitVec.toNat / y.toBitVec.toNat : Nat) : Int) := by
      rw [Int.fdiv_eq_ediv]; simp
    rw [hfd, BitVec.ofInt_natCast]
    show _ = x.toBitVec.udiv y.toBitVec
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_udiv]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.toNat_lt

cake_primitive ConPastel.Impl.u64modP
  (Exp.fn (ofString "b") (.if_ (.app .equality [w2i (V "b"), .lit (.intLit 0)]) (V "p")
    (i2w (.app (.arith .mod .intT) [w2i (V "p"), w2i (V "b")])))) by
  intro envC funs hnodup hfind _ _ _
  refine prim2g_cert envC funs _ hnodup hfind fun x xv y yv ha hb => ?_
  have hbi := Eval_w64_to_int (Eval_u64_w hb)
  have hai := Eval_w64_to_int (Eval_u64_w ha)
  refine Eval_if (Eval_int_eq hbi (Eval_lit _ (.intLit 0) (INT 0) rfl)) (fun h => ?_) (fun h => ?_)
  · have hy : y = 0 := UInt64.toNat_inj.mp (by simpa using h)
    subst hy
    exact Eval_w_u64 (Eval_u64_w ha) (by
      show x.toBitVec = x.toBitVec.umod (0 : UInt64).toBitVec; simp)
  · have h0 : y.toBitVec.toNat ≠ 0 := by simpa using h
    refine Eval_w_u64 (Eval_int_to_w64 (Eval_int_mod (by exact_mod_cast h0) hai hbi)) ?_
    have hfm : ((x.toBitVec.toNat : Int)).fmod (y.toBitVec.toNat : Int) =
        ((x.toBitVec.toNat % y.toBitVec.toNat : Nat) : Int) := by
      rw [Int.fmod_eq_emod]; simp
    rw [hfm, BitVec.ofInt_natCast]
    show _ = x.toBitVec.umod y.toBitVec
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_umod]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.toNat_lt

cake_replace UInt64.shiftRight ConPastel.Impl.shiftRightF ConPastel.Impl.shiftRight_eq_F
cake_replace UInt64.mul ConPastel.Impl.mulF ConPastel.Impl.mul_eq_F
cake_replace UInt64.div ConPastel.Impl.divF ConPastel.Impl.div_eq_F
cake_replace UInt64.mod ConPastel.Impl.modF ConPastel.Impl.mod_eq_F
cake_replace instDecidableEqUInt64 ConPastel.Impl.u64DecEqI ConPastel.Impl.instDecidableEqUInt64_eq
