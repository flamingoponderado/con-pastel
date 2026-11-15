import ConPastel.Translator.Lemmas

/-! # Pairs, represented as CakeML tuples `conv none [a, b]` -/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.EvaluateHOL

def PAIR {α β : Type} (A : RefInv α) (B : RefInv β) : RefInv (α × β) :=
  fun p v => ∃ av bv, A p.1 av ∧ B p.2 bv ∧ v = .conv none [av, bv]

theorem Eval_pair {α β : Type} {A : RefInv α} {B : RefInv β} {env : SemEnv Value} {ea eb : Exp}
    {a : α} {b : β} (ha : Eval env ea (A a)) (hb : Eval env eb (B b)) :
    Eval env (.con none [ea, eb]) (PAIR A B (a, b)) := by
  intro σ s
  have hall : EvalAll env [eb, ea] [B b, A a] := ⟨hb, ha, trivial⟩
  obtain ⟨vs, refs, ⟨a₁, a₂, hrun⟩, hvs⟩ := hall.runs σ s
  match vs, hvs with
  | [bv, av], .cons hbv (.cons hav .nil) =>
    refine ⟨.conv none [av, bv], refs, ⟨a₁, a₂, ?_⟩, av, bv, hav, hbv, rfl⟩
    rw [evaluate]
    simp [doConCheck, hrun, buildConv]

/-- Destructuring a pair: `case e of (x, y) => body`. -/
theorem Eval_mat_pair {α β γ : Type} {A : RefInv α} {B : RefInv β} {C : RefInv γ}
    {env : SemEnv Value} {e body : Exp} {x y : VarN} {p : α × β} {f : α → β → γ}
    (hxy : x ≠ y) (he : Eval env e (PAIR A B p))
    (hb : ∀ a b, p = (a, b) → ∀ av bv, A a av → B b bv →
      Eval (clauseEnv env [x, y] [av, bv]) body (C (f a b))) :
    Eval env (.mat e [(.pcon none [.pvar x, .pvar y], body)]) (C (f p.1 p.2)) := by
  intro σ s
  obtain ⟨v, r₁, ⟨a₁, a₂, ha⟩, av, bv, hav, hbv, rfl⟩ := he σ s
  obtain ⟨w, r₂, ⟨b₁, b₂, hbr⟩, qw⟩ := hb p.1 p.2 rfl av bv hav hbv σ { s with refs := s.refs ++ r₁ }
  refine ⟨w, r₁ ++ r₂, ⟨b₁ + a₁, a₂ + b₂, ?_⟩, qw⟩
  have ha' := Runs.add_clock ha (by simp) b₁
  have hfix : fixClock { s with clock := b₁ + a₁ } ({ s with refs := s.refs ++ r₁, clock := b₁ + a₂ },
      (Result.val [.conv none [av, bv]] : Result (List Value) Value)) =
      ({ s with refs := s.refs ++ r₁, clock := b₁ + a₂ }, .val [.conv none [av, bv]]) := by
    rw [← ha']; exact fixClock_evaluate _ env _
  rw [evaluate]
  simp only [ha', hfix, headValue, Flapjack.holHd]
  have hcan : canPmatchAll env.c (s.refs ++ r₁) [.pcon none [.pvar x, .pvar y]] (.conv none [av, bv]) := by
    simp [canPmatchAll, pmatch, pmatchList]
  simp only [List.map_cons, List.map_nil, hcan, ite_true]
  rw [evaluateMatch]
  have hnd : (patBindings (.pcon none [.pvar x, .pvar y])).Nodup := by
    simp [patBindings, patsBindings, hxy.symm]
  simp only [hnd, ite_true]
  have hpm : pmatch env.c (s.refs ++ r₁) (.pcon none [.pvar x, .pvar y]) (.conv none [av, bv]) [] =
      .match [(y, bv), (x, av)] := by
    simp [pmatch, pmatchList]
  rw [hpm]
  rw [Nat.add_comm b₁ a₂]
  have := Runs.add_clock hbr (by simp) a₂
  simpa [clauseEnv, List.append_assoc] using this

/-! ## Dependent variants (results whose type depends on the arguments) -/

theorem Eval_mat_pair_dep {α β : Type} {γ : α → β → Type} {A : RefInv α} {B : RefInv β}
    {C : (a : α) → (b : β) → RefInv (γ a b)}
    {env : SemEnv Value} {e body : Exp} {x y : VarN} {p : α × β} {f : (a : α) → (b : β) → γ a b}
    (hxy : x ≠ y) (he : Eval env e (PAIR A B p))
    (hb : ∀ a b, p = (a, b) → ∀ av bv, A a av → B b bv →
      Eval (clauseEnv env [x, y] [av, bv]) body (C a b (f a b))) :
    Eval env (.mat e [(.pcon none [.pvar x, .pvar y], body)]) (C p.1 p.2 (f p.1 p.2)) :=
  Eval_mat_pair (C := fun (Q : Value → Prop) v => Q v) (f := fun a b => C a b (f a b)) hxy he hb

/-- Lean's termination relation may mention the fixed parameters (`rP q`, at
the argument tuple `q`): recursion keeps them, so the relation on tuples is
"same fixed part, and Lean's relation there on the packed values". -/
theorem wf_fiber {τ : Sort u} {α : Sort v} (rP : τ → α → α → Prop) (pk : τ → α)
    (h : ∀ q, WellFounded (rP q)) :
    WellFounded (fun a b => rP a = rP b ∧ rP b (pk a) (pk b)) := by
  have aux : ∀ (R : α → α → Prop) c, Acc R c → ∀ q, rP q = R → pk q = c →
      Acc (fun a b => rP a = rP b ∧ rP b (pk a) (pk b)) q := by
    intro R c hc
    induction hc with
    | intro c _ ih =>
      intro q hq hc
      constructor
      intro p ⟨hp, hr⟩
      rw [hq, hc] at hr
      exact ih (pk p) hr p (hp.trans hq) rfl
  exact ⟨fun q => aux (rP q) (pk q) ((h q).apply (pk q)) q rfl rfl⟩

theorem darrow_of_wf {α : Type} {β : α → Type} {A : RefInv α} {B : (x : α) → RefInv (β x)}
    {r : α → α → Prop} (hwf : WellFounded r) {f : (x : α) → β x} {cl : Value}
    (h : ∀ x, (∀ y, r y x → ∀ yv, A y yv → AppReturns cl yv (B y (f y))) →
      ∀ xv, A x xv → AppReturns cl xv (B x (f x))) :
    DARROW A B f cl := by
  intro x
  induction x using hwf.induction with
  | _ x ih => exact h x ih

theorem Eval_app_ihd {α : Type} {β : α → Type} {A : RefInv α} {B : (x : α) → RefInv (β x)}
    {env : SemEnv Value} {ef ex : Exp} {cl : Value} {f : (x : α) → β x} {y : α}
    (hf : Eval env ef (· = cl)) (hx : Eval env ex (A y))
    (ih : ∀ yv, A y yv → AppReturns cl yv (B y (f y))) :
    Eval env (.app .opapp [ef, ex]) (B y (f y)) :=
  Eval_app hf hx fun _ yv hfv hy => hfv ▸ ih yv hy

end ConPastel.Translator
