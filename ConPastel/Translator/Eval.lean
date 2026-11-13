import Flapjack.EvaluateProps.ClockIoConsequences
import Flapjack.EvaluateHOL.ClockFull

/-!
# The refinement judgement

Lean counterpart of CakeML's `ml_translator` judgement `Eval env exp P`:
from any state, `exp` evaluates (at some clock) to a value satisfying `P`,
leaving the state unchanged except for the clock and for store cells
appended at the end. Pure translated code never touches the FFI, so the
judgement quantifies over every FFI state type.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL

/-- `e` evaluates from `s` to the value `v`, ending in `s'`, for some
starting and ending clocks. -/
def EvalRel {σ : Type} (s : State σ) (env : SemEnv Value) (e : Exp) (s' : State σ)
    (v : Value) : Prop :=
  ∃ ck₁ ck₂, evaluate { s with clock := ck₁ } env [e] = ({ s' with clock := ck₂ }, .val [v])

/-- The refinement judgement: `e` evaluates in `env` to a value satisfying
`P`, from every state, only appending to the store. -/
def Eval (env : SemEnv Value) (e : Exp) (P : Value → Prop) : Prop :=
  ∀ {σ : Type} (s : State σ), ∃ v refs, EvalRel s env e { s with refs := s.refs ++ refs } v ∧ P v

/-- Applying the function value `f` to `x` returns a value satisfying `P`. -/
def AppReturns (f x : Value) (P : Value → Prop) : Prop :=
  ∀ {σ : Type} (s : State σ), ∃ env e, doOpApp [f, x] = some (env, e) ∧
    ∃ v refs, EvalRel s env e { s with refs := s.refs ++ refs } v ∧ P v

/-! ## Clocks -/

theorem State.with_clock_with_clock {σ : Type} (s : State σ) (a b : Nat) :
    ({ { s with clock := a } with clock := b } : State σ) = { s with clock := b } := rfl

theorem State.with_clock_self {σ : Type} (s : State σ) : ({ s with clock := s.clock } : State σ) = s :=
  rfl

/-- Adding to the starting clock adds to the ending clock. -/
theorem evaluate_add_clock {σ : Type} {s s' : State σ} {env : SemEnv Value} {es : List Exp}
    {ck₁ ck₂ : Nat} {r : Result (List Value) Value}
    (h : evaluate { s with clock := ck₁ } env es = ({ s' with clock := ck₂ }, r))
    (hr : r ≠ .err (.abort .timeoutError)) (extra : Nat) :
    evaluate { s with clock := ck₁ + extra } env es = ({ s' with clock := ck₂ + extra }, r) :=
  EvaluateProps.evaluate_addToClock { s with clock := ck₁ } env es { s' with clock := ck₂ } r extra ⟨h, hr⟩

theorem EvalRel.add_clock {σ : Type} {s s' : State σ} {env : SemEnv Value} {e : Exp} {v : Value}
    {ck₁ ck₂ : Nat} (h : evaluate { s with clock := ck₁ } env [e] = ({ s' with clock := ck₂ }, .val [v]))
    (extra : Nat) :
    evaluate { s with clock := ck₁ + extra } env [e] = ({ s' with clock := ck₂ + extra }, .val [v]) :=
  evaluate_add_clock h (by simp) extra

/-- The clamp `fixClock` is the identity on evaluations. -/
theorem fixClock_evaluate {σ : Type} (s : State σ) (env : SemEnv Value) (es : List Exp) :
    fixClock s (evaluate s env es) = evaluate s env es :=
  (fixClockEvaluate s env es []).1

/-! ## Basic expressions -/

theorem Eval_lit (env : SemEnv Value) (l : Lit) (P : Value → Prop) (h : P (.litv l)) :
    Eval env (.lit l) P := by
  intro σ s
  refine ⟨.litv l, [], ⟨0, 0, ?_⟩, h⟩
  simp [evaluate]

theorem Eval_var (env : SemEnv Value) (n : Ident ModN VarN) (v : Value) (P : Value → Prop)
    (hlook : nsLookup env.v n = some v) (h : P v) : Eval env (.var n) P := by
  intro σ s
  refine ⟨v, [], ⟨0, 0, ?_⟩, h⟩
  simp [evaluate, hlook]

theorem Eval_fn (env : SemEnv Value) (n : VarN) (body : Exp) (P : Value → Prop)
    (h : P (.closure env n body)) : Eval env (.fn n body) P := by
  intro σ s
  refine ⟨_, [], ⟨0, 0, ?_⟩, h⟩
  simp [evaluate]

theorem Eval_weaken {env : SemEnv Value} {e : Exp} {P Q : Value → Prop} (h : Eval env e P)
    (hPQ : ∀ v, P v → Q v) : Eval env e Q := by
  intro σ s
  obtain ⟨v, refs, hrel, hp⟩ := h s
  exact ⟨v, refs, hrel, hPQ v hp⟩

/-! ## Running expression lists -/

/-- `es` runs from `s` to `s'` with result `r`, at some clocks. -/
def Runs {σ : Type} (s : State σ) (env : SemEnv Value) (es : List Exp) (s' : State σ)
    (r : Result (List Value) Value) : Prop :=
  ∃ ck₁ ck₂, evaluate { s with clock := ck₁ } env es = ({ s' with clock := ck₂ }, r)

theorem EvalRel.runs {σ : Type} {s s' : State σ} {env : SemEnv Value} {e : Exp} {v : Value}
    (h : EvalRel s env e s' v) : Runs s env [e] s' (.val [v]) := h

theorem Runs.evalRel {σ : Type} {s s' : State σ} {env : SemEnv Value} {e : Exp} {v : Value}
    (h : Runs s env [e] s' (.val [v])) : EvalRel s env e s' v := h

theorem Runs.add_clock {σ : Type} {s s' : State σ} {env : SemEnv Value} {es : List Exp}
    {r : Result (List Value) Value} {ck₁ ck₂ : Nat}
    (h : evaluate { s with clock := ck₁ } env es = ({ s' with clock := ck₂ }, r))
    (hr : r ≠ .err (.abort .timeoutError)) (extra : Nat) :
    evaluate { s with clock := extra + ck₁ } env es = ({ s' with clock := extra + ck₂ }, r) := by
  rw [Nat.add_comm extra ck₁, Nat.add_comm extra ck₂]
  exact evaluate_add_clock h hr extra

theorem evaluate_cons_val {σ : Type} {s s₁ s₂ : State σ} {env : SemEnv Value} {e : Exp}
    {es : List Exp} {v : Value} {vs : List Value}
    (h₁ : evaluate s env [e] = (s₁, .val [v])) (h₂ : evaluate s₁ env (e' :: es) = (s₂, .val vs)) :
    evaluate s env (e :: e' :: es) = (s₂, .val (v :: vs)) := by
  rw [evaluate, fixClock_evaluate, h₁]
  simp [h₂, headValue, Flapjack.holHd]

theorem Runs.cons {σ : Type} {s s₁ s₂ : State σ} {env : SemEnv Value} {e e' : Exp}
    {es : List Exp} {v : Value} {vs : List Value}
    (h₁ : Runs s env [e] s₁ (.val [v])) (h₂ : Runs s₁ env (e' :: es) s₂ (.val vs)) :
    Runs s env (e :: e' :: es) s₂ (.val (v :: vs)) := by
  obtain ⟨a₁, a₂, ha⟩ := h₁
  obtain ⟨b₁, b₂, hb⟩ := h₂
  refine ⟨b₁ + a₁, a₂ + b₂, ?_⟩
  have ha' := Runs.add_clock ha (by simp) b₁
  have hb' := Runs.add_clock hb (by simp) a₂
  rw [Nat.add_comm a₂ b₁] at hb'
  exact evaluate_cons_val ha' hb'

/-- Application of a function value, once its argument list has run. -/
theorem evaluate_app_opapp {σ : Type} {s s₁ : State σ} {env env' : SemEnv Value}
    {ef ex body : Exp} {vf vx : Value}
    (hargs : evaluate s env [ex, ef] = (s₁, .val [vx, vf]))
    (happ : doOpApp [vf, vx] = some (env', body)) (hclock : s₁.clock ≠ 0) :
    evaluate s env [.app .opapp [ef, ex]] = evaluate (decClock s₁) env' [body] := by
  have hfix : fixClock s (s₁, (Result.val [vx, vf] : Result (List Value) Value)) = (s₁, .val [vx, vf]) := by
    rw [← hargs]; exact fixClock_evaluate s env _
  rw [evaluate]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, hargs, hfix]
  simp [getOpClass, happ, hclock]

theorem Runs.app_opapp {σ : Type} {s s₁ s₂ : State σ} {env env' : SemEnv Value}
    {ef ex body : Exp} {vf vx v : Value}
    (hargs : Runs s env [ex, ef] s₁ (.val [vx, vf]))
    (happ : doOpApp [vf, vx] = some (env', body))
    (hbody : Runs s₁ env' [body] s₂ (.val [v])) :
    Runs s env [.app .opapp [ef, ex]] s₂ (.val [v]) := by
  obtain ⟨a₁, a₂, ha⟩ := hargs
  obtain ⟨b₁, b₂, hb⟩ := hbody
  refine ⟨(b₁ + 1) + a₁, a₂ + b₂, ?_⟩
  have ha' := Runs.add_clock ha (by simp) (b₁ + 1)
  rw [evaluate_app_opapp ha' happ (by simp)]
  have hb' := Runs.add_clock hb (by simp) a₂
  have : decClock { s₁ with clock := b₁ + 1 + a₂ } = { s₁ with clock := a₂ + b₁ } := by
    simp [decClock]; omega
  rw [this]
  exact hb'

/-- States reached by appending to the store. -/
theorem State.refs_append {σ : Type} (s : State σ) (r₁ r₂ : Store Value) :
    ({ { s with refs := s.refs ++ r₁ } with refs := s.refs ++ r₁ ++ r₂ } : State σ) =
      { s with refs := s.refs ++ (r₁ ++ r₂) } := by
  simp [List.append_assoc]

theorem Eval_app {env : SemEnv Value} {ef ex : Exp} {Pf Px Q : Value → Prop}
    (hf : Eval env ef Pf) (hx : Eval env ex Px)
    (h : ∀ fv xv, Pf fv → Px xv → AppReturns fv xv Q) :
    Eval env (.app .opapp [ef, ex]) Q := by
  intro σ s
  obtain ⟨vx, r₁, hx₁, px⟩ := hx s
  obtain ⟨vf, r₂, hf₁, pf⟩ := hf { s with refs := s.refs ++ r₁ }
  obtain ⟨env', body, happ, vr, r₃, hb, q⟩ := h vf vx pf px
    { s with refs := s.refs ++ (r₁ ++ r₂) }
  refine ⟨vr, r₁ ++ r₂ ++ r₃, ?_, q⟩
  have hargs := Runs.cons hx₁.runs (State.refs_append s r₁ r₂ ▸ hf₁.runs)
  have := Runs.app_opapp hargs happ hb.runs
  apply Runs.evalRel
  simpa [List.append_assoc] using this

end ConPastel.Translator
