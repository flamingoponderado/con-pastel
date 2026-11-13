import ConPastel.Translator.Eval

/-!
# Refinement invariants and the basic combinator lemmas

Invariants relate a Lean value to the CakeML value representing it
(CakeML's `INT`, `NUM`, `BOOL`, `-->`).
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL

/-- A refinement invariant for Lean type `α`. -/
abbrev RefInv (α : Type) := α → Value → Prop

def INT : RefInv Int := fun i v => v = .litv (.intLit i)
def NAT : RefInv Nat := fun n v => v = .litv (.intLit n)
def BOOL : RefInv Bool := fun b v => v = boolValue b

/-- Functions: applying the value to a representation of `x` returns a
representation of `f x`. -/
def Arrow {α β : Type} (a : RefInv α) (b : RefInv β) : RefInv (α → β) :=
  fun f fv => ∀ x xv, a x xv → AppReturns fv xv (b (f x))

/-! ## Functions -/

theorem Eval_fn_arrow {α β : Type} {a : RefInv α} {b : RefInv β} {env : SemEnv Value} {n : VarN}
    {body : Exp} {f : α → β}
    (h : ∀ x xv, a x xv → Eval { env with v := nsBind n xv env.v } body (b (f x))) :
    Eval env (.fn n body) (Arrow a b f) := by
  apply Eval_fn
  intro x xv hx σ s
  obtain ⟨v, refs, hrel, hv⟩ := h x xv hx σ s
  exact ⟨_, _, rfl, v, refs, hrel, hv⟩

theorem Eval_app_arrow {α β : Type} {a : RefInv α} {b : RefInv β} {env : SemEnv Value} {ef ex : Exp}
    {f : α → β} {x : α} (hf : Eval env ef (Arrow a b f)) (hx : Eval env ex (a x)) :
    Eval env (.app .opapp [ef, ex]) (b (f x)) :=
  Eval_app hf hx fun _ _ hfv hxv => hfv x _ hxv

/-! ## let -/

theorem evaluate_let_val {σ : Type} {s s₁ : State σ} {env : SemEnv Value} {n : Option VarN}
    {e₁ e₂ : Exp} {v : Value} (h₁ : evaluate s env [e₁] = (s₁, .val [v])) :
    evaluate s env [.let_ n e₁ e₂] = evaluate s₁ { env with v := nsOptBind n v env.v } [e₂] := by
  have hfix : fixClock s (s₁, (Result.val [v] : Result (List Value) Value)) = (s₁, .val [v]) := by
    rw [← h₁]; exact fixClock_evaluate s env _
  rw [evaluate]
  simp [h₁, hfix, headValue, Flapjack.holHd]

theorem Runs.let_ {σ : Type} {s s₁ s₂ : State σ} {env : SemEnv Value} {n : Option VarN}
    {e₁ e₂ : Exp} {v : Value} {r : Result (List Value) Value}
    (h₁ : Runs s env [e₁] s₁ (.val [v]))
    (h₂ : Runs s₁ { env with v := nsOptBind n v env.v } [e₂] s₂ r)
    (hr : r ≠ .err (.abort .timeoutError)) :
    Runs s env [.let_ n e₁ e₂] s₂ r := by
  obtain ⟨a₁, a₂, ha⟩ := h₁
  obtain ⟨b₁, b₂, hb⟩ := h₂
  refine ⟨b₁ + a₁, a₂ + b₂, ?_⟩
  rw [evaluate_let_val (Runs.add_clock ha (by simp) b₁)]
  rw [Nat.add_comm b₁ a₂]
  exact Runs.add_clock hb hr a₂

theorem Eval_let {env : SemEnv Value} {n : Option VarN} {e₁ e₂ : Exp} {P Q : Value → Prop}
    (h₁ : Eval env e₁ P) (h₂ : ∀ v, P v → Eval { env with v := nsOptBind n v env.v } e₂ Q) :
    Eval env (.let_ n e₁ e₂) Q := by
  intro σ s
  obtain ⟨v, r₁, hv, pv⟩ := h₁ σ s
  obtain ⟨w, r₂, hw, qw⟩ := h₂ v pv σ { s with refs := s.refs ++ r₁ }
  refine ⟨w, r₁ ++ r₂, ?_, qw⟩
  apply Runs.evalRel
  have := Runs.let_ hv.runs hw.runs (by simp)
  simpa [List.append_assoc] using this

/-! ## if -/

theorem evaluate_if_val {σ : Type} {s s₁ : State σ} {env : SemEnv Value} {c e₂ e₃ : Exp}
    {b : Bool} (h₁ : evaluate s env [c] = (s₁, .val [boolValue b])) :
    evaluate s env [.if_ c e₂ e₃] = evaluate s₁ env [if b then e₂ else e₃] := by
  have hfix : fixClock s (s₁, (Result.val [boolValue b] : Result (List Value) Value)) =
      (s₁, .val [boolValue b]) := by
    rw [← h₁]; exact fixClock_evaluate s env _
  rw [evaluate]
  simp only [h₁, hfix, headValue, Flapjack.holHd]
  split
  · next h => simp [doIf_boolValue] at h
  · next e h => simp [doIf_boolValue] at h; subst h; rfl

theorem Runs.if_ {σ : Type} {s s₁ s₂ : State σ} {env : SemEnv Value} {c e₂ e₃ : Exp} {b : Bool}
    {r : Result (List Value) Value}
    (h₁ : Runs s env [c] s₁ (.val [boolValue b]))
    (h₂ : Runs s₁ env [if b then e₂ else e₃] s₂ r) (hr : r ≠ .err (.abort .timeoutError)) :
    Runs s env [.if_ c e₂ e₃] s₂ r := by
  obtain ⟨a₁, a₂, ha⟩ := h₁
  obtain ⟨b₁, b₂, hb⟩ := h₂
  refine ⟨b₁ + a₁, a₂ + b₂, ?_⟩
  rw [evaluate_if_val (Runs.add_clock ha (by simp) b₁)]
  rw [Nat.add_comm b₁ a₂]
  exact Runs.add_clock hb hr a₂

theorem Eval_if {env : SemEnv Value} {c e₂ e₃ : Exp} {b : Bool} {P : Value → Prop}
    (hc : Eval env c (BOOL b)) (h₂ : b = true → Eval env e₂ P) (h₃ : b = false → Eval env e₃ P) :
    Eval env (.if_ c e₂ e₃) P := by
  intro σ s
  obtain ⟨v, r₁, hv, pv⟩ := hc σ s
  cases pv
  have hbr : Eval env (if b then e₂ else e₃) P := by
    cases b
    · exact h₃ rfl
    · exact h₂ rfl
  obtain ⟨w, r₂, hw, qw⟩ := hbr σ { s with refs := s.refs ++ r₁ }
  refine ⟨w, r₁ ++ r₂, ?_, qw⟩
  apply Runs.evalRel
  have := Runs.if_ hv.runs hw.runs (by simp)
  simpa [List.append_assoc] using this

/-! ## Primitive operations -/

theorem evaluate_app_simple {σ : Type} {s s₁ : State σ} {env : SemEnv Value} {op : Op}
    {args : List Exp} {vs : List Value} {refs : Store Value} {ffi : HolFfiState σ}
    {r : Result Value Value}
    (hargs : evaluate s env args.reverse = (s₁, .val vs)) (hclass : getOpClass op = .simple)
    (happ : doApp (s₁.refs, s₁.ffi) op vs.reverse = some ((refs, ffi), r)) :
    evaluate s env [.app op args] = ({ s₁ with refs, ffi }, listResult r) := by
  have hfix : fixClock s (s₁, (Result.val vs : Result (List Value) Value)) = (s₁, .val vs) := by
    rw [← hargs]; exact fixClock_evaluate s env _
  rw [evaluate]
  simp [hargs, hfix, hclass, happ]

/-- A pure binary primitive: arguments evaluate right to left, then the
operation computes a value without touching the store or the FFI. -/
theorem Eval_binop {env : SemEnv Value} {op : Op} {e₁ e₂ : Exp} {P₁ P₂ Q : Value → Prop}
    (hclass : getOpClass op = .simple) (h₁ : Eval env e₁ P₁) (h₂ : Eval env e₂ P₂)
    (hop : ∀ v₁ v₂, P₁ v₁ → P₂ v₂ → ∃ v, Q v ∧
      ∀ {σ : Type} (refs : Store Value) (ffi : HolFfiState σ),
        doApp (refs, ffi) op [v₁, v₂] = some ((refs, ffi), .val v)) :
    Eval env (.app op [e₁, e₂]) Q := by
  intro σ s
  obtain ⟨v₂, r₂, hv₂, p₂⟩ := h₂ σ s
  obtain ⟨v₁, r₁, hv₁, p₁⟩ := h₁ σ { s with refs := s.refs ++ r₂ }
  obtain ⟨v, qv, hdo⟩ := hop v₁ v₂ p₁ p₂
  refine ⟨v, r₂ ++ r₁, ?_, qv⟩
  have hargs := Runs.cons hv₂.runs (State.refs_append s r₂ r₁ ▸ hv₁.runs)
  obtain ⟨a₁, a₂, ha⟩ := hargs
  refine ⟨a₁, a₂, ?_⟩
  have := evaluate_app_simple (args := [e₁, e₂]) (by simpa using ha) hclass (hdo _ _)
  simpa [listResult] using this

theorem doApp_int {σ : Type} (refs : Store Value) (ffi : HolFfiState σ) (action : Arith)
    (a b : Int) (hact : action = .add ∨ action = .sub ∨ action = .mul) :
    doApp (refs, ffi) (.arith action .intT) [.litv (.intLit a), .litv (.intLit b)] =
      some ((refs, ffi), .val (.litv (.intLit (match action with
        | .add => a + b | .sub => a - b | _ => a * b)))) := by
  rcases hact with rfl | rfl | rfl <;> simp [doApp_arith_core, doAppNumericCore]

theorem Eval_int_add {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Int}
    (h₁ : Eval env e₁ (INT a)) (h₂ : Eval env e₂ (INT b)) :
    Eval env (.app (.arith .add .intT) [e₁, e₂]) (INT (a + b)) :=
  Eval_binop rfl h₁ h₂ fun v₁ v₂ p₁ p₂ => by
    subst p₁ p₂
    exact ⟨_, rfl, fun refs ffi => doApp_int refs ffi .add a b (by simp)⟩

theorem Eval_int_sub {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Int}
    (h₁ : Eval env e₁ (INT a)) (h₂ : Eval env e₂ (INT b)) :
    Eval env (.app (.arith .sub .intT) [e₁, e₂]) (INT (a - b)) :=
  Eval_binop rfl h₁ h₂ fun v₁ v₂ p₁ p₂ => by
    subst p₁ p₂
    exact ⟨_, rfl, fun refs ffi => doApp_int refs ffi .sub a b (by simp)⟩

theorem Eval_int_mul {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Int}
    (h₁ : Eval env e₁ (INT a)) (h₂ : Eval env e₂ (INT b)) :
    Eval env (.app (.arith .mul .intT) [e₁, e₂]) (INT (a * b)) :=
  Eval_binop rfl h₁ h₂ fun v₁ v₂ p₁ p₂ => by
    subst p₁ p₂
    exact ⟨_, rfl, fun refs ffi => doApp_int refs ffi .mul a b (by simp)⟩

/-! ## Integer comparisons -/

theorem intCmp_spec (a b : Int) :
    intCmp .lt a b = decide (a < b) ∧ intCmp .leq a b = decide (a ≤ b) ∧
    intCmp .gt a b = decide (a > b) ∧ intCmp .geq a b = decide (a ≥ b) := by
  simp only [intCmp]
  rcases Int.lt_trichotomy a b with h | h | h
  · have : compare a b = .lt := Int.compare_eq_lt.mpr h
    simp only [this, h, Int.le_of_lt h, Int.not_le.mpr h, decide_true, decide_false,
      gt_iff_lt, Int.not_lt.mpr (Int.le_of_lt h)]
    decide
  · subst h
    have : compare a a = .eq := Int.compare_eq_eq.mpr rfl
    simp only [this, Int.lt_irrefl, Int.le_refl, decide_true, decide_false, gt_iff_lt, ge_iff_le]
    decide
  · have : compare a b = .gt := Int.compare_eq_gt.mpr h
    simp only [this, h, Int.le_of_lt h, Int.not_le.mpr h, decide_true, decide_false,
      Int.not_lt.mpr (Int.le_of_lt h)]
    decide

theorem Eval_int_cmp {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Int} (op : Opb)
    (h₁ : Eval env e₁ (INT a)) (h₂ : Eval env e₂ (INT b)) :
    Eval env (.app (.test (.compare op) .intT) [e₁, e₂]) (BOOL (intCmp op a b)) :=
  Eval_binop rfl h₁ h₂ fun v₁ v₂ p₁ p₂ => by
    subst p₁ p₂
    exact ⟨_, rfl, fun refs ffi => by simp [doApp, doTest]⟩

theorem Eval_int_eq {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Int}
    (h₁ : Eval env e₁ (INT a)) (h₂ : Eval env e₂ (INT b)) :
    Eval env (.app .equality [e₁, e₂]) (BOOL (decide (a = b))) :=
  Eval_binop rfl h₁ h₂ fun v₁ v₂ p₁ p₂ => by
    subst p₁ p₂
    exact ⟨_, rfl, fun refs ffi => by
      simp [doApp, doAppNumericCore, doAppBasic, doEq, litSameType]⟩

end ConPastel.Translator
