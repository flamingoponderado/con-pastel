import ConPastel.Translator.Recursion
import Batteries.Data.List.Basic

/-!
# Constructors and flat constructor matches

Lean `casesOn` trees are translated to CakeML matches whose clauses are
exactly one flat pattern `C x₁ … xₙ` per constructor. This file gives the
semantics of such matches and of constructor applications.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL

/-! ## Evaluating argument lists -/

/-- Each expression satisfies the corresponding invariant. -/
def EvalAll (env : SemEnv Value) : List Exp → List (Value → Prop) → Prop
  | [], [] => True
  | e :: es, P :: Ps => Eval env e P ∧ EvalAll env es Ps
  | _, _ => False

theorem evaluate_nil {σ : Type} (s : State σ) (env : SemEnv Value) :
    evaluate s env [] = (s, .val []) := by
  rw [evaluate]

theorem EvalAll.runs {env : SemEnv Value} :
    ∀ {es : List Exp} {Ps : List (Value → Prop)}, EvalAll env es Ps →
      ∀ (σ : Type) (s : State σ), ∃ vs refs,
        Runs s env es { s with refs := s.refs ++ refs } (.val vs) ∧
        List.Forall₂ (fun P v => P v) Ps vs
  | [], [], _, σ, s => ⟨[], [], ⟨0, 0, by simp [evaluate_nil]⟩, .nil⟩
  | [e], [P], ⟨he, _⟩, σ, s => by
    obtain ⟨v, refs, hv, pv⟩ := he σ s
    exact ⟨[v], refs, hv.runs, .cons pv .nil⟩
  | e :: e' :: es, P :: P' :: Ps, ⟨he, hrest⟩, σ, s => by
    obtain ⟨v, r₁, hv, pv⟩ := he σ s
    obtain ⟨vs, r₂, hvs, pvs⟩ := EvalAll.runs hrest σ { s with refs := s.refs ++ r₁ }
    refine ⟨v :: vs, r₁ ++ r₂, ?_, .cons pv pvs⟩
    have := Runs.cons hv.runs (State.refs_append s r₁ r₂ ▸ hvs)
    simpa [List.append_assoc] using this
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
  | [_], _ :: _ :: _, ⟨_, h⟩, _, _ => h.elim
  | _ :: _ :: _, [_], ⟨_, h⟩, _, _ => h.elim

/-! ## Constructor applications -/

theorem Eval_con {env : SemEnv Value} {c : ConN} {args : List Exp} {stamp : Stamp}
    {Ps : List (Value → Prop)}
    (hlook : nsLookup env.c (.short c) = some (args.length, stamp))
    (hargs : EvalAll env args.reverse Ps) :
    Eval env (.con (some (.short c)) args)
      (fun v => ∃ vs, List.Forall₂ (fun P v => P v) Ps vs ∧ v = .conv (some stamp) vs.reverse) := by
  intro σ s
  obtain ⟨vs, refs, ⟨a₁, a₂, ha⟩, pvs⟩ := hargs.runs σ s
  refine ⟨_, refs, ⟨a₁, a₂, ?_⟩, vs, pvs, rfl⟩
  rw [evaluate]
  simp [doConCheck, hlook, ha, buildConv]

/-! ## Flat constructor matches -/

/-- The clause for constructor `c` binding `xs`. -/
def conClause (c : ConN) (xs : List VarN) (body : Exp) : Pat × Exp :=
  (.pcon (some (.short c)) (xs.map .pvar), body)

theorem patsBindings_pvars (xs : List VarN) : patsBindings (xs.map .pvar) = xs.reverse := by
  induction xs with
  | nil => simp [patsBindings]
  | cons x xs ih => simp [patsBindings, patBindings, ih]

theorem pmatchList_pvars (envC : Namespace ModN ConN (Nat × Stamp)) (store : Store Value) :
    ∀ (xs : List VarN) (vs : List Value) (acc : List (VarN × Value)), xs.length = vs.length →
      pmatchList envC store (xs.map .pvar) vs acc = .match ((xs.zip vs).reverse ++ acc)
  | [], [], acc, _ => by simp [pmatchList]
  | x :: xs, v :: vs, acc, h => by
    rw [List.map_cons, pmatchList, pmatch]
    simp only
    rw [pmatchList_pvars envC store xs vs _ (by simpa using h)]
    simp
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- The match clauses for a list of flat constructor cases. -/
def conClauses (cases : List (ConN × List VarN × Exp)) : List (Pat × Exp) :=
  cases.map fun (c, xs, b) => conClause c xs b

/-- The hypotheses under which a flat match over `cases` behaves as a case
split: every constructor is in scope with the arity of its clause and the
type stamp `tn`, constructor names are distinct, and each clause binds
distinct variables. -/
structure FlatCases (envC : Namespace ModN ConN (Nat × Stamp)) (tn : Nat)
    (cases : List (ConN × List VarN × Exp)) : Prop where
  lookup : ∀ c xs b, (c, xs, b) ∈ cases → nsLookup envC (.short c) = some (xs.length, .typeStamp c tn)
  nodupC : (cases.map (·.1)).Nodup
  nodupX : ∀ c xs b, (c, xs, b) ∈ cases → xs.Nodup

theorem FlatCases.tail {envC : Namespace ModN ConN (Nat × Stamp)} {tn : Nat} {hd}
    {cases : List (ConN × List VarN × Exp)} (h : FlatCases envC tn (hd :: cases)) :
    FlatCases envC tn cases :=
  ⟨fun c xs b hm => h.lookup c xs b (.tail _ hm), (List.nodup_cons.mp (by simpa using h.nodupC)).2,
    fun c xs b hm => h.nodupX c xs b (.tail _ hm)⟩

theorem nodup_reverse' {α : Type} {l : List α} (h : l.Nodup) : l.reverse.Nodup :=
  List.pairwise_reverse.mpr (h.imp Ne.symm)

theorem mem_nodup_key {α β γ : Type} :
    ∀ {l : List (α × β × γ)} {a : α} {x₁ x₂ : β} {y₁ y₂ : γ}, (l.map (·.1)).Nodup →
      (a, x₁, y₁) ∈ l → (a, x₂, y₂) ∈ l → x₁ = x₂ ∧ y₁ = y₂
  | [], _, _, _, _, _, _, h₁, _ => by simp at h₁
  | (a', x', y') :: l, a, x₁, x₂, y₁, y₂, hnd, h₁, h₂ => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h₁ with e₁ | e₁ <;> rcases List.mem_cons.mp h₂ with e₂ | e₂
    · cases e₁; cases e₂; exact ⟨rfl, rfl⟩
    · cases e₁; exact (hnd.1 (List.mem_map.mpr ⟨_, e₂, rfl⟩)).elim
    · cases e₂; exact (hnd.1 (List.mem_map.mpr ⟨_, e₁, rfl⟩)).elim
    · exact mem_nodup_key hnd.2 e₁ e₂

/-- Matching one flat clause against a value of the same type: the
constructor clause matches, any other constructor does not. -/
theorem pmatch_conClause {envC : Namespace ModN ConN (Nat × Stamp)} {store : Store Value}
    {c c' : ConN} {xs' : List VarN} {tn : Nat} {vals : List Value}
    (hlook : nsLookup envC (.short c') = some (xs'.length, .typeStamp c' tn)) :
    pmatch envC store (.pcon (some (.short c')) (xs'.map .pvar)) (.conv (some (.typeStamp c tn)) vals) [] =
      if c' = c then (if vals.length = xs'.length then .match ((xs'.zip vals).reverse) else .typeError)
      else .noMatch := by
  rw [pmatch]
  simp only [hlook, sameType, sameCtor, List.length_map, beq_self_eq_true, Bool.and_self,
    ite_true, Stamp.typeStamp.injEq, and_true, decide_eq_true_eq]
  by_cases hc : c' = c
  · subst hc
    by_cases hl : vals.length = xs'.length
    · simp [hl, pmatchList_pvars envC store xs' vals [] hl.symm]
    · simp [hl]
  · simp [hc]

theorem evaluateMatch_flat {σ : Type} {s : State σ} {env : SemEnv Value} {tn : Nat}
    {err : Value} :
    ∀ {cases : List (ConN × List VarN × Exp)} {c : ConN} {xs : List VarN} {b : Exp}
      {vals : List Value}, FlatCases env.c tn cases → (c, xs, b) ∈ cases → vals.length = xs.length →
      evaluateMatch s env (.conv (some (.typeStamp c tn)) vals) (conClauses cases) err =
        evaluate s { env with v := nsAppend (alistToNs (xs.zip vals).reverse) env.v } [b]
  | [], _, _, _, _, _, hm, _ => by simp at hm
  | (c', xs', b') :: cases, c, xs, b, vals, hf, hm, hl => by
    have hlook := hf.lookup c' xs' b' (.head _)
    have hnd : (patBindings (.pcon (some (.short c')) (xs'.map .pvar))).Nodup := by
      simpa [patBindings, patsBindings_pvars] using
        nodup_reverse' (hf.nodupX c' xs' b' (.head _))
    simp only [conClauses, List.map_cons, conClause]
    rw [evaluateMatch]
    simp only [hnd, ite_true, pmatch_conClause (store := s.refs) (vals := vals) hlook]
    by_cases hc : c' = c
    · subst hc
      -- the matched case is the head: names are distinct
      have hnot : ∀ xs₀ b₀, (c', xs₀, b₀) ∈ cases → False := by
        intro xs₀ b₀ h₀
        have := hf.nodupC
        simp only [List.map_cons, List.nodup_cons] at this
        exact this.1 (List.mem_map.mpr ⟨_, h₀, rfl⟩)
      rcases List.mem_cons.mp hm with h | h
      · cases h
        simp [hl]
      · exact (hnot _ _ h).elim
    · simp only [hc, ite_false]
      have hm' : (c, xs, b) ∈ cases := by
        rcases List.mem_cons.mp hm with h | h
        · cases h; exact absurd rfl hc
        · exact h
      exact evaluateMatch_flat hf.tail hm' hl

theorem canPmatchAll_flat {envC : Namespace ModN ConN (Nat × Stamp)} {store : Store Value}
    {tn : Nat} {cases : List (ConN × List VarN × Exp)} {c : ConN} {xs : List VarN} {b : Exp}
    {vals : List Value} (hf : FlatCases envC tn cases) (hm : (c, xs, b) ∈ cases)
    (hl : vals.length = xs.length) :
    canPmatchAll envC store ((conClauses cases).map Prod.fst) (.conv (some (.typeStamp c tn)) vals) := by
  simp only [canPmatchAll, List.all_eq_true, List.mem_map, conClauses, conClause]
  rintro _ ⟨_, ⟨⟨c', xs', b'⟩, hm', rfl⟩, rfl⟩
  rw [pmatch_conClause (hf.lookup c' xs' b' hm')]
  by_cases hc : c' = c
  · subst hc
    obtain ⟨rfl, -⟩ := mem_nodup_key hf.nodupC hm hm'
    simp [hl]
  · simp [hc]

theorem nsLookup_nsAppend_alist_short {β : Type} (al : List (VarN × β)) (e : Namespace ModN VarN β)
    (n : VarN) :
    nsLookup (nsAppend (alistToNs al) e) (.short n) =
      match al.lookup n with
      | some x => some x
      | none => nsLookup e (.short n) := by
  cases e with
  | bind vs ms =>
    simp only [alistToNs, nsAppend, nsLookup_bind_short]
    induction al with
    | nil => simp [List.lookup]
    | cons p al ih =>
      obtain ⟨k, x⟩ := p
      by_cases h : n = k
      · simp [List.lookup, h]
      · have : (n == k) = false := beq_eq_false_iff_ne.mpr h
        simp [List.lookup, this, ih]

/-- The environment a flat clause body runs in. -/
def clauseEnv (env : SemEnv Value) (xs : List VarN) (vals : List Value) : SemEnv Value :=
  { env with v := nsAppend (alistToNs (xs.zip vals).reverse) env.v }

theorem evaluate_mat_flat {σ : Type} {s s₁ : State σ} {env : SemEnv Value} {e : Exp} {tn : Nat}
    {cases : List (ConN × List VarN × Exp)} {c : ConN} {xs : List VarN} {b : Exp}
    {vals : List Value} (hf : FlatCases env.c tn cases) (hm : (c, xs, b) ∈ cases)
    (hl : vals.length = xs.length)
    (he : evaluate s env [e] = (s₁, .val [.conv (some (.typeStamp c tn)) vals])) :
    evaluate s env [.mat e (conClauses cases)] = evaluate s₁ (clauseEnv env xs vals) [b] := by
  have hfix : fixClock s (s₁, (Result.val [.conv (some (.typeStamp c tn)) vals] :
      Result (List Value) Value)) = (s₁, .val [.conv (some (.typeStamp c tn)) vals]) := by
    rw [← he]; exact fixClock_evaluate s env _
  rw [evaluate]
  simp only [he, hfix, headValue, Flapjack.holHd, canPmatchAll_flat (store := s₁.refs) hf hm hl,
    ite_true]
  exact evaluateMatch_flat hf hm hl

theorem Eval_mat {env : SemEnv Value} {e : Exp} {tn : Nat} {cases : List (ConN × List VarN × Exp)}
    {P Q : Value → Prop} (hf : FlatCases env.c tn cases) (he : Eval env e P)
    (hcase : ∀ v, P v → ∃ c xs b vals, (c, xs, b) ∈ cases ∧
      v = .conv (some (.typeStamp c tn)) vals ∧ vals.length = xs.length ∧
      Eval (clauseEnv env xs vals) b Q) :
    Eval env (.mat e (conClauses cases)) Q := by
  intro σ s
  obtain ⟨v, r₁, ⟨a₁, a₂, ha⟩, pv⟩ := he σ s
  obtain ⟨c, xs, b, vals, hm, rfl, hl, hb⟩ := hcase v pv
  obtain ⟨w, r₂, ⟨b₁, b₂, hbr⟩, qw⟩ := hb σ { s with refs := s.refs ++ r₁ }
  refine ⟨w, r₁ ++ r₂, ⟨b₁ + a₁, a₂ + b₂, ?_⟩, qw⟩
  rw [evaluate_mat_flat hf hm hl (Runs.add_clock ha (by simp) b₁)]
  rw [Nat.add_comm b₁ a₂]
  have := Runs.add_clock hbr (by simp) a₂
  simpa [List.append_assoc] using this

end ConPastel.Translator
