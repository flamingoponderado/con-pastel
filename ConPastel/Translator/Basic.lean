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
abbrev Inv (α : Type) := α → Value → Prop

def INT : Inv Int := fun i v => v = .litv (.intLit i)
def NAT : Inv Nat := fun n v => v = .litv (.intLit n)
def BOOL : Inv Bool := fun b v => v = boolValue b

/-- Functions: applying the value to a representation of `x` returns a
representation of `f x`. -/
def Arrow {α β : Type} (a : Inv α) (b : Inv β) : Inv (α → β) :=
  fun f fv => ∀ x xv, a x xv → AppReturns fv xv (b (f x))

/-! ## Functions -/

theorem Eval_fn_arrow {α β : Type} {a : Inv α} {b : Inv β} {env : SemEnv Value} {n : VarN}
    {body : Exp} {f : α → β}
    (h : ∀ x xv, a x xv → Eval { env with v := nsBind n xv env.v } body (b (f x))) :
    Eval env (.fn n body) (Arrow a b f) := by
  apply Eval_fn
  intro x xv hx σ s
  obtain ⟨v, refs, hrel, hv⟩ := h x xv hx s
  exact ⟨_, _, rfl, v, refs, hrel, hv⟩

theorem Eval_app_arrow {α β : Type} {a : Inv α} {b : Inv β} {env : SemEnv Value} {ef ex : Exp}
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
  obtain ⟨v, r₁, hv, pv⟩ := h₁ s
  obtain ⟨w, r₂, hw, qw⟩ := h₂ v pv { s with refs := s.refs ++ r₁ }
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
  obtain ⟨v, r₁, hv, pv⟩ := hc s
  cases pv
  have hbr : Eval env (if b then e₂ else e₃) P := by
    cases b
    · exact h₃ rfl
    · exact h₂ rfl
  obtain ⟨w, r₂, hw, qw⟩ := hbr { s with refs := s.refs ++ r₁ }
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
  obtain ⟨v₂, r₂, hv₂, p₂⟩ := h₂ s
  obtain ⟨v₁, r₁, hv₁, p₁⟩ := h₁ { s with refs := s.refs ++ r₂ }
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

end ConPastel.Translator
