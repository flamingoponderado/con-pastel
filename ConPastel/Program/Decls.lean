import ConPastel.Translator.Eval
import ConPastel.Translator.Recursion
import Batteries.Tactic.OpenPrivate

/-!
# Running declarations

`DeclsRun s env ds s' env'`: the declarations `ds` run from `s` in `env` to
`s'`, producing the new bindings `env'`, at some clocks.
-/

namespace ConPastel.Program
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL ConPastel.Translator
open private everyExpList everyExpClauses everyExpFuns from Flapjack.AstHOL.Syntax

def DeclsRun {σ : Type} (s : State σ) (env : SemEnv Value) (ds : List Dec) (s' : State σ)
    (env' : SemEnv Value) : Prop :=
  ∃ ck₁ ck₂, evaluateDecs { s with clock := ck₁ } env ds = ({ s' with clock := ck₂ }, .val env')

theorem fixClock_evaluateDecs {σ : Type} (s : State σ) (env : SemEnv Value) (ds : List Dec) :
    fixClock s (evaluateDecs s env ds) = evaluateDecs s env ds :=
  (fixClockEvaluate s env [] ds).2

theorem evaluateDecs_add_clock {σ : Type} {s s' : State σ} {env env' : SemEnv Value} {ds : List Dec}
    {ck₁ ck₂ : Nat}
    (h : evaluateDecs { s with clock := ck₁ } env ds = ({ s' with clock := ck₂ }, .val env'))
    (extra : Nat) :
    evaluateDecs { s with clock := extra + ck₁ } env ds = ({ s' with clock := extra + ck₂ }, .val env') := by
  rw [Nat.add_comm extra ck₁, Nat.add_comm extra ck₂]
  exact EvaluateProps.evaluateDecs_addToClock { s with clock := ck₁ } env ds { s' with clock := ck₂ } _
    extra ⟨h, by simp⟩

theorem evaluateDecs_nil {σ : Type} (s : State σ) (env : SemEnv Value) :
    evaluateDecs s env [] = (s, .val { v := nsEmpty, c := nsEmpty }) := by
  rw [evaluateDecs]; rfl

theorem DeclsRun.nil {σ : Type} (s : State σ) (env : SemEnv Value) :
    DeclsRun s env [] s { v := nsEmpty, c := nsEmpty } :=
  ⟨0, 0, by simp [evaluateDecs_nil]⟩

theorem DeclsRun.cons {σ : Type} {s s₁ s₂ : State σ} {env e₁ e₂ : SemEnv Value} {d d' : Dec}
    {ds : List Dec} (h₁ : DeclsRun s env [d] s₁ e₁)
    (h₂ : DeclsRun s₁ (extendDecEnv e₁ env) (d' :: ds) s₂ e₂) :
    DeclsRun s env (d :: d' :: ds) s₂ (extendDecEnv e₂ e₁) := by
  obtain ⟨a₁, a₂, ha⟩ := h₁
  obtain ⟨b₁, b₂, hb⟩ := h₂
  refine ⟨b₁ + a₁, a₂ + b₂, ?_⟩
  have ha' := evaluateDecs_add_clock ha b₁
  have hb' := evaluateDecs_add_clock hb a₂
  rw [Nat.add_comm a₂ b₁] at hb'
  rw [evaluateDecs, fixClock_evaluateDecs, ha']
  simp only [hb']
  simp [combineDecResult, extendDecEnv]

/-- `Dlet x e`. -/
theorem DeclsRun.dlet {σ : Type} {s s₁ : State σ} {env : SemEnv Value} {loc : Flapjack.Misc.Location.Locs}
    {x : VarN} {e : Exp} {v : Value} (hcon : everyExp (oneConCheck env.c) e = true)
    (h : Runs s env [e] s₁ (.val [v])) :
    DeclsRun s env [.dlet loc (.pvar x) e] s₁ { v := alistToNs [(x, v)], c := nsEmpty } := by
  obtain ⟨a₁, a₂, ha⟩ := h
  refine ⟨a₁, a₂, ?_⟩
  rw [evaluateDecs]
  simp [patBindings, hcon, ha, headValue, Flapjack.holHd, pmatch]

/-- `Dlet _ e`. -/
theorem DeclsRun.dlet_any {σ : Type} {s s₁ : State σ} {env : SemEnv Value}
    {loc : Flapjack.Misc.Location.Locs} {e : Exp} {v : Value}
    (hcon : everyExp (oneConCheck env.c) e = true) (h : Runs s env [e] s₁ (.val [v])) :
    DeclsRun s env [.dlet loc .pany e] s₁ { v := alistToNs [], c := nsEmpty } := by
  obtain ⟨a₁, a₂, ha⟩ := h
  refine ⟨a₁, a₂, ?_⟩
  rw [evaluateDecs]
  simp [patBindings, hcon, ha, headValue, Flapjack.holHd, pmatch]

/-- `Dletrec funs`. -/
theorem DeclsRun.dletrec {σ : Type} (s : State σ) {env : SemEnv Value}
    {loc : Flapjack.Misc.Location.Locs} {funs : List (VarN × VarN × Exp)}
    (hnodup : (funs.map fun (f, _, _) => f).Nodup)
    (hcon : funs.all (fun (_, _, e) => everyExp (oneConCheck env.c) e) = true) :
    DeclsRun s env [.dletrec loc funs] s { v := buildRecEnv funs env nsEmpty, c := nsEmpty } := by
  refine ⟨0, 0, ?_⟩
  rw [evaluateDecs]
  simp [hnodup, hcon]

/-- `Dtype tds`. -/
theorem DeclsRun.dtype {σ : Type} (s : State σ) {env : SemEnv Value}
    {loc : Flapjack.Misc.Location.Locs} {tds : TypeDef} (hdup : tds.all checkDupCtors = true) :
    DeclsRun s env [.dtype loc tds] { s with nextTypeStamp := s.nextTypeStamp + tds.length }
      { v := nsEmpty, c := buildTdefs s.nextTypeStamp tds } := by
  refine ⟨0, 0, ?_⟩
  rw [evaluateDecs]
  simp [hdup]

end ConPastel.Program
