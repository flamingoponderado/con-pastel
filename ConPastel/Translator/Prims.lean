import ConPastel.Translator.Meta.Primitive

/-!
# Primitive units for `Nat`

CakeML integers implement `Nat` directly, except where Lean's operations are
total in a way CakeML's are not: truncated subtraction, and division and
modulo by zero.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString

theorem nat_beq_eq_decide (x y : Nat) : Nat.beq x y = decide (x = y) := by
  rcases Bool.eq_false_or_eq_true (Nat.beq x y) with h | h
  · simp [Nat.eq_of_beq_eq_true h]
  · simp [h, Nat.ne_of_beq_eq_false h]

theorem nat_ble_eq_decide (x y : Nat) : Nat.ble x y = decide (x ≤ y) := by
  rcases Bool.eq_false_or_eq_true (Nat.ble x y) with h | h
  · simp [h, Nat.le_of_ble_eq_true h]
  · have hn : ¬ x ≤ y := fun hle => by rw [Nat.ble_eq_true_of_le hle] at h; cases h
    simp [h, hn]

/-- Lookups of the two arguments of a curried primitive body. -/
theorem prim_lookup_p (envC : SemEnv Value) (funs : List (VarN × VarN × Exp)) (xv yv : Value) :
    nsLookup (nsBind (ofString "b") yv (recBodyEnv envC funs (ofString "p") xv).v) (.short (ofString "p")) =
      some xv := by
  simp +decide [recBodyEnv, nsLookup_nsBind_short]

theorem prim_lookup_b (envC : SemEnv Value) (funs : List (VarN × VarN × Exp)) (xv yv : Value) :
    nsLookup (nsBind (ofString "b") yv (recBodyEnv envC funs (ofString "p") xv).v) (.short (ofString "b")) =
      some yv := by
  simp [nsLookup_nsBind_short]

/-- Certificates of curried two-argument primitives on `Nat`. -/
theorem prim2_cert {β : Type} {B : RefInv β} {f : Nat → Nat → β} {body : Exp}
    (envC : SemEnv Value) (funs : List (VarN × VarN × Exp)) (n : VarN)
    (hnodup : (funs.map fun (f, _, _) => f).Nodup)
    (hfind : findRecFun n funs = some (ofString "p", .fn (ofString "b") body))
    (h : ∀ x xv y yv, NAT x xv → NAT y yv →
      Eval { v := nsBind (ofString "b") yv (recBodyEnv envC funs (ofString "p") xv).v,
             c := (recBodyEnv envC funs (ofString "p") xv).c } body (B (f x y))) :
    Arrow NAT (Arrow NAT B) f (.recclosure envC funs n) := by
  intro x xv hx
  apply AppReturns_recclosure hnodup hfind
  apply Eval_fn_arrow
  intro y yv hy
  exact h x xv y yv hx hy

/-- Dependent two-argument primitives (e.g. `Decidable (n = m)` results). -/
theorem prim2d_cert {β : Nat → Nat → Type} {B : (x y : Nat) → RefInv (β x y)} {f : (x y : Nat) → β x y}
    {body : Exp} (envC : SemEnv Value) (funs : List (VarN × VarN × Exp)) (n : VarN)
    (hnodup : (funs.map fun (f, _, _) => f).Nodup)
    (hfind : findRecFun n funs = some (ofString "p", .fn (ofString "b") body))
    (h : ∀ x xv y yv, NAT x xv → NAT y yv →
      Eval (SemEnv.mk (nsBind (ofString "b") yv (recBodyEnv envC funs (ofString "p") xv).v)
             (recBodyEnv envC funs (ofString "p") xv).c) body (B x y (f x y))) :
    DARROW NAT (fun x => DARROW NAT (fun y => B x y)) f (.recclosure envC funs n) := by
  intro x xv hx
  apply AppReturns_recclosure hnodup hfind
  apply Eval_fn_darrow
  intro y yv hy
  exact h x xv y yv hx hy

/-- The two argument variables of a primitive body. -/
theorem prim_args (envC : SemEnv Value) (funs : List (VarN × VarN × Exp)) (x y : Nat) (xv yv : Value)
    (hx : NAT x xv) (hy : NAT y yv) :
    Eval (SemEnv.mk (nsBind (ofString "b") yv (recBodyEnv envC funs (ofString "p") xv).v)
      (recBodyEnv envC funs (ofString "p") xv).c) (V "p") (NAT x) ∧
    Eval (SemEnv.mk (nsBind (ofString "b") yv (recBodyEnv envC funs (ofString "p") xv).v)
      (recBodyEnv envC funs (ofString "p") xv).c) (V "b") (NAT y) :=
  ⟨Eval_var _ _ xv _ (prim_lookup_p envC funs xv yv) hx, Eval_var _ _ yv _ (prim_lookup_b envC funs xv yv) hy⟩

end ConPastel.Translator

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive Nat.sub
  (Exp.fn (ofString "b") (.if_ (.app (.test (.compare .lt) .intT) [V "p", V "b"]) (.lit (.intLit 0))
    (.app (.arith .sub .intT) [V "p", V "b"])))
by
  intro envC funs hnodup hfind _ _ _
  refine prim2_cert envC funs _ hnodup hfind ?_
  intro x xv y yv hx hy
  let E : SemEnv Value := SemEnv.mk (nsBind (ofString "b") yv (recBodyEnv envC funs (ofString "p") xv).v)
    (recBodyEnv envC funs (ofString "p") xv).c
  have ha : Eval E (V "p") (INT x) := Eval_var E _ xv (INT x) (prim_lookup_p envC funs xv yv) hx
  have hb : Eval E (V "b") (INT y) := Eval_var E _ yv (INT y) (prim_lookup_b envC funs xv yv) hy
  refine Eval_if (Eval_int_cmp .lt ha hb) (fun h => ?_) (fun h => ?_)
  · exact Eval_lit _ _ _ (by
      have : (x : Int) < y := by simpa [(intCmp_spec _ _).1] using h
      simp [NAT]; omega)
  · exact Eval_weaken (Eval_int_sub ha hb) fun w hw => by
      have : ¬ (x : Int) < y := by simpa [(intCmp_spec _ _).1] using h
      simp only [INT] at hw; simp only [NAT, hw, Nat.sub_eq]; congr 2; omega

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive Nat.div
  (Exp.fn (ofString "b") (.if_ (.app .equality [V "b", .lit (.intLit 0)]) (.lit (.intLit 0))
    (.app (.arith .div .intT) [V "p", V "b"])))
by
  intro envC funs hnodup hfind _ _ _
  refine prim2_cert envC funs _ hnodup hfind ?_
  intro x xv y yv hx hy
  obtain ⟨ha, hb⟩ := prim_args envC funs x y xv yv hx hy
  refine Eval_if (Eval_nat_eq hb (Eval_nat_lit _ 0)) (fun h => ?_) (fun h => ?_)
  · have : y = 0 := of_decide_eq_true h
    subst this; exact Eval_lit _ _ _ (by show NAT (x / 0) _; simp [NAT])
  · have : y ≠ 0 := of_decide_eq_false h
    exact Eval_weaken (Eval_int_div (by exact_mod_cast this) ha hb) fun w hw => by
      have hfd : (x : Int).fdiv (y : Int) = ((x / y : Nat) : Int) := by
        rw [Int.fdiv_eq_ediv]; simp
      simp only [INT] at hw
      show NAT (x / y) w
      simp only [NAT, hw, hfd]

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive Nat.beq
  (Exp.fn (ofString "b") (.app .equality [V "p", V "b"]))
by
  intro envC funs hnodup hfind _ _ _
  refine prim2_cert envC funs _ hnodup hfind ?_
  intro x xv y yv hx hy
  obtain ⟨ha, hb⟩ := prim_args envC funs x y xv yv hx hy
  exact Eval_weaken (Eval_nat_eq ha hb) fun w hw => by
    simpa [BOOL, nat_beq_eq_decide] using hw

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive Nat.ble
  (Exp.fn (ofString "b") (.app (.test (.compare .leq) .intT) [V "p", V "b"]))
by
  intro envC funs hnodup hfind _ _ _
  refine prim2_cert envC funs _ hnodup hfind ?_
  intro x xv y yv hx hy
  obtain ⟨ha, hb⟩ := prim_args envC funs x y xv yv hx hy
  exact Eval_weaken (Eval_nat_le ha hb) fun w hw => by
    simpa [BOOL, nat_ble_eq_decide] using hw

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive Nat.decEq
  (Exp.fn (ofString "b") (.app .equality [V "p", V "b"]))
by
  intro envC funs hnodup hfind _ _ _
  refine prim2d_cert envC funs _ hnodup hfind ?_
  intro x xv y yv hx hy
  obtain ⟨ha, hb⟩ := prim_args envC funs x y xv yv hx hy
  exact Eval_nat_eq ha hb

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive Nat.decLt
  (Exp.fn (ofString "b") (.app (.test (.compare .lt) .intT) [V "p", V "b"]))
by
  intro envC funs hnodup hfind _ _ _
  refine prim2d_cert envC funs _ hnodup hfind ?_
  intro x xv y yv hx hy
  obtain ⟨ha, hb⟩ := prim_args envC funs x y xv yv hx hy
  exact Eval_nat_lt ha hb

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive Nat.decLe
  (Exp.fn (ofString "b") (.app (.test (.compare .leq) .intT) [V "p", V "b"]))
by
  intro envC funs hnodup hfind _ _ _
  refine prim2d_cert envC funs _ hnodup hfind ?_
  intro x xv y yv hx hy
  obtain ⟨ha, hb⟩ := prim_args envC funs x y xv yv hx hy
  exact Eval_nat_le ha hb

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive Nat.mod
  (Exp.fn (ofString "b") (.if_ (.app .equality [V "b", .lit (.intLit 0)]) (V "p")
    (.app (.arith .mod .intT) [V "p", V "b"])))
by
  intro envC funs hnodup hfind _ _ _
  refine prim2_cert envC funs _ hnodup hfind ?_
  intro x xv y yv hx hy
  obtain ⟨ha, hb⟩ := prim_args envC funs x y xv yv hx hy
  refine Eval_if (Eval_nat_eq hb (Eval_nat_lit _ 0)) (fun h => ?_) (fun h => ?_)
  · have : y = 0 := of_decide_eq_true h
    subst this
    exact Eval_weaken ha fun w hw => by show NAT (x % 0) w; simpa using hw
  · have : y ≠ 0 := of_decide_eq_false h
    exact Eval_weaken (Eval_int_mod (by exact_mod_cast this) ha hb) fun w hw => by
      have hfm : (x : Int).fmod (y : Int) = ((x % y : Nat) : Int) := by
        rw [Int.fmod_eq_emod]; simp
      simp only [INT] at hw
      show NAT (x % y) w
      simp only [NAT, hw, hfm]
