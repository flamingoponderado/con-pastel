import ConPastel.Program.Groups
import ConPastel.Semantics.Behaviour
import ConPastel.Par.Work

/-!
# Declarations that end: normally or by an FFI call ending the run

`DeclsRun` (`ConPastel.Program.Decls`) is a run of declarations that succeeds. A process of the
parallel checker may also end by an FFI call that ends the run (`abort`, or a worker running out of
claims), so its main declarations are described by `DeclsEnd`, with any result. `program_end`
turns such a run of the whole program into a terminating behaviour of `semanticsProg`.
-/

namespace ConPastel.Par
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.SemanticsHOL
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString ConPastel.Translator ConPastel.Program

/-- A run of declarations with result `r`. -/
def DeclsEnd {σ : Type} (s : State σ) (env : SemEnv Value) (ds : List Dec) (s' : State σ)
    (r : Result (SemEnv Value) Value) : Prop :=
  ∃ ck₁ ck₂, evaluateDecs { s with clock := ck₁ } env ds = ({ s' with clock := ck₂ }, r)

/-- A declaration result that is not a timeout or a type error. -/
def DecEnded (r : Result (SemEnv Value) Value) : Prop :=
  (∃ e, r = .val e) ∨ ∃ ev, r = .err (.abort (.ffiError ev))

theorem DecEnded.not_timeout {r : Result (SemEnv Value) Value} (h : DecEnded r) :
    r ≠ .err (.abort .timeoutError) := by
  rcases h with ⟨e, rfl⟩ | ⟨ev, rfl⟩ <;> simp

theorem evaluateDecs_add_clock' {σ : Type} {s s' : State σ} {env : SemEnv Value} {ds : List Dec}
    {ck₁ ck₂ : Nat} {r : Result (SemEnv Value) Value}
    (h : evaluateDecs { s with clock := ck₁ } env ds = ({ s' with clock := ck₂ }, r))
    (hr : r ≠ .err (.abort .timeoutError)) (extra : Nat) :
    evaluateDecs { s with clock := extra + ck₁ } env ds = ({ s' with clock := extra + ck₂ }, r) := by
  rw [Nat.add_comm extra ck₁, Nat.add_comm extra ck₂]
  exact EvaluateProps.evaluateDecs_addToClock { s with clock := ck₁ } env ds { s' with clock := ck₂ } _
    extra ⟨h, hr⟩

theorem DeclsEnd.of_run {σ : Type} {s s' : State σ} {env env' : SemEnv Value} {ds : List Dec}
    (h : DeclsRun s env ds s' env') : DeclsEnd s env ds s' (.val env') := h

theorem DeclsEnd.cons {σ : Type} {s s₁ s₂ : State σ} {env e₁ : SemEnv Value} {d d' : Dec}
    {ds : List Dec} {r : Result (SemEnv Value) Value} (h₁ : DeclsRun s env [d] s₁ e₁)
    (h₂ : DeclsEnd s₁ (extendDecEnv e₁ env) (d' :: ds) s₂ r) (hr : DecEnded r) :
    DeclsEnd s env (d :: d' :: ds) s₂ (combineDecResult e₁ r) := by
  obtain ⟨a₁, a₂, ha⟩ := h₁
  obtain ⟨b₁, b₂, hb⟩ := h₂
  refine ⟨b₁ + a₁, a₂ + b₂, ?_⟩
  have ha' := evaluateDecs_add_clock ha b₁
  have hb' := evaluateDecs_add_clock' hb hr.not_timeout a₂
  rw [Nat.add_comm a₂ b₁] at hb'
  rw [evaluateDecs, fixClock_evaluateDecs, ha']
  simp only [hb']

theorem DecEnded.combine {r : Result (SemEnv Value) Value} (h : DecEnded r) (e₁ : SemEnv Value) :
    DecEnded (combineDecResult e₁ r) := by
  rcases h with ⟨e, rfl⟩ | ⟨ev, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨ev, rfl⟩

/-- `Dlet _ e` whose expression ends the run. -/
theorem DeclsEnd.dlet_abort {σ : Type} {s s₁ : State σ} {env : SemEnv Value}
    {loc : Flapjack.Misc.Location.Locs} {e : Exp} {a : Abort}
    (hcon : everyExp (oneConCheck env.c) e = true) (h : Runs s env [e] s₁ (.err (.abort a))) :
    DeclsEnd s env [.dlet loc .pany e] s₁ (.err (.abort a)) := by
  obtain ⟨a₁, a₂, ha⟩ := h
  refine ⟨a₁, a₂, ?_⟩
  rw [evaluateDecs]
  simp [patBindings, hcon, ha]

/-- `Dlet _ e` that ends, normally or not. -/
theorem DeclsEnd.dlet_ended {σ : Type} {s s₁ : State σ} {env : SemEnv Value}
    {loc : Flapjack.Misc.Location.Locs} {e : Exp} {r : Result (List Value) Value}
    (hcon : everyExp (oneConCheck env.c) e = true) (h : Runs s env [e] s₁ r) (hr : Ended r) :
    ∃ r', DeclsEnd s env [.dlet loc .pany e] s₁ r' ∧ DecEnded r' ∧
      ∀ ev, r = .err (.abort (.ffiError ev)) → r' = .err (.abort (.ffiError ev)) := by
  rcases hr with rfl | ⟨ev, rfl⟩
  · exact ⟨_, .of_run (DeclsRun.dlet_any hcon h), .inl ⟨_, rfl⟩, by simp⟩
  · exact ⟨_, DeclsEnd.dlet_abort hcon h, .inr ⟨ev, rfl⟩, by simp⟩

/-- The groups before a main program that ends. -/
theorem groups_end {σ : Type} (c : Namespace ModN ConN (Nat × Stamp)) (loc : Flapjack.Misc.Location.Locs) :
    ∀ (gs : List (List Fn)) (L : List (VarN × Value)) (d : Dec) (ds : List Dec) (s s' : State σ)
      (r : Result (SemEnv Value) Value), GroupsOk c gs → DecEnded r →
      DeclsEnd s (flatEnv c (bindsAfter c gs L)) (d :: ds) s' r →
      ∃ r', DeclsEnd s (flatEnv c L) (gs.map (Dec.dletrec loc) ++ d :: ds) s' r' ∧ DecEnded r' ∧
        ∀ ev, r = .err (.abort (.ffiError ev)) → r' = .err (.abort (.ffiError ev))
  | [], _, _, _, _, _, r, _, hr, h => ⟨r, h, hr, fun _ h => h⟩
  | g :: gs, L, d, ds, s, s', r, hok, hr, h => by
    obtain ⟨⟨hnd, hcon⟩, hok⟩ := hok
    have h₁ := DeclsRun.dletrec (loc := loc) (env := flatEnv c L) s hnd hcon
    obtain ⟨r₂, h₂, hr₂, hf₂⟩ := groups_end c loc gs _ d ds s s' r hok hr h
    rw [← extend_flat] at h₂
    refine ⟨_, ?_, hr₂.combine _, fun ev he => by rw [hf₂ ev he]; rfl⟩
    cases gs with
    | nil => exact DeclsEnd.cons h₁ h₂ hr₂
    | cons g' gs' => exact DeclsEnd.cons h₁ h₂ hr₂

/-- The outcome of a declaration result that ended. -/
def outcomeOf : Result (SemEnv Value) Value → HolOutcome
  | .err (.abort (.ffiError ev)) => .ffiOutcome ev
  | _ => .success

/-- **A program run that ended is a terminating behaviour.** -/
theorem program_end {σ : Type} {st s' : State σ} {env : SemEnv Value} {prog : List Dec}
    {r : Result (SemEnv Value) Value} (h : DeclsEnd st env prog s' r) (hr : DecEnded r)
    (hck : st.clock = 0) :
    semanticsProg st env prog (.terminate (outcomeOf r) s'.ffi.ioEvents) := by
  obtain ⟨ck₁, ck₂, heval⟩ := h
  refine ⟨ck₁, s'.ffi, r, ?_, ?_, rfl, ?_⟩
  · simp only [SemanticsHOL.evaluateProgWithClock]
    have : ({ st with clock := ck₁ } : State σ) = { st with clock := ck₁ } := rfl
    rw [heval]
  · rcases hr with ⟨e, rfl⟩ | ⟨ev, rfl⟩
    · exact ⟨by simp, rfl⟩
    · rfl
  · rcases hr with ⟨e, rfl⟩ | ⟨ev, rfl⟩ <;> simp

end ConPastel.Par
