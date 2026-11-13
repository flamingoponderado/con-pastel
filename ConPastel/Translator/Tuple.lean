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

end ConPastel.Translator
