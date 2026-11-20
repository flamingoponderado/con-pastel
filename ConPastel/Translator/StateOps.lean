import ConPastel.Translator.Record

/-!
# Map operations on a state record's fields

The operations a state record (`recRel`) supports, on the Lean state: a
field's map is named by its projection `get` (and, to write it, the record
update `set`). Each is, on the field's table, a map operation of
`ConPastel.Translator.HashMapM` (`sim_*`), which `EvalM_lens` turns into code.

`hmInsertD` writes the field as con-leche's memo updates do: the map is
detached (the field set to `∅`) before the insertion is stored.
-/

namespace ConPastel.Translator
universe u v
open Std.DHashMap.Internal
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.NamespaceHOL

section
variable {σ ε K V α : Type} [BEq K] [Hashable K]

/-- `(get st)[k]?`. -/
def hmFind (get : σ → Std.HashMap K V) (k : K) : StateT σ (Except ε) (Option V) :=
  fun st => .ok ((get st)[k]?, st)

/-- Insert into the field, detaching it first. -/
def hmInsertD (get : σ → Std.HashMap K V) (set : σ → Std.HashMap K V → σ) (k : K) (v : V) :
    StateT σ (Except ε) Unit :=
  fun st => .ok ((), set (set st ∅) ((get st).insert k v))

/-- `(get st).size`. -/
def hmSize (get : σ → Std.HashMap K V) : StateT σ (Except ε) Nat :=
  fun st => .ok ((get st).size, st)

/-- Empty the field (`get` names it). -/
def hmClear (_get : σ → Std.HashMap K V) (set : σ → Std.HashMap K V → σ) : StateT σ (Except ε) Unit :=
  fun st => .ok ((), set st ∅)

/-- A plain part of the state. -/
def stRead (f : σ → α) : StateT σ (Except ε) α := fun st => .ok (f st, st)

end

/-! ## Each is a table operation on its field -/

section
variable {σ ε : Type} {tabs : σ → List TEntry} {P : σ → Value → Prop} {i : Nat}
  {K V : Type} [BEq K] [Hashable K] {BI : RefInv (Bkt K V)} {get : σ → Std.HashMap K V}

theorem raw0_of (m : Std.HashMap K V) : (⟨m.inner.1, m.inner.2.size_buckets_pos⟩ : Raw₀ K (fun _ => V)) =
    ⟨m.inner.1, m.inner.2.size_buckets_pos⟩ := rfl

theorem sim_find (hlen : ∀ st, i < (tabs st).length)
    (hent : ∀ st, (tabs st)[i]'(hlen st) = ⟨K, V, BI, (get st).inner.1⟩) (k : K) :
    ∀ st, ∃ a raw' st', (getM k : StateT (TRaw K V) (Except ε) (Option V)) (get st).inner.1 = .ok (a, raw') ∧
      (hmFind get k : StateT σ (Except ε) (Option V)) st = .ok (a, st') ∧
      tabs st' = (tabs st).set i ⟨K, V, BI, raw'⟩ ∧ ∀ v, P st' v ↔ P st v := by
  intro st
  refine ⟨_, _, st, getM_eq ⟨(get st).inner.1, (get st).inner.2.size_buckets_pos⟩ k, rfl, ?_, fun _ => Iff.rfl⟩
  rw [← hent st, List.set_getElem_self]

theorem sim_size (hlen : ∀ st, i < (tabs st).length)
    (hent : ∀ st, (tabs st)[i]'(hlen st) = ⟨K, V, BI, (get st).inner.1⟩) :
    ∀ st, ∃ a raw' st', (sizeM : StateT (TRaw K V) (Except ε) Nat) (get st).inner.1 = .ok (a, raw') ∧
      (hmSize get : StateT σ (Except ε) Nat) st = .ok (a, st') ∧
      tabs st' = (tabs st).set i ⟨K, V, BI, raw'⟩ ∧ ∀ v, P st' v ↔ P st v := by
  intro st
  refine ⟨_, _, st, sizeM_eq _, rfl, ?_, fun _ => Iff.rfl⟩
  rw [← hent st, List.set_getElem_self]

theorem sim_insert {set : σ → Std.HashMap K V → σ}
    (htabs : ∀ st m, tabs (set (set st ∅) m) = (tabs st).set i ⟨K, V, BI, m.inner.1⟩)
    (hP : ∀ st m v, P (set (set st ∅) m) v ↔ P st v) (k : K) (v : V) :
    ∀ st, ∃ a raw' st', (insertM k v : StateT (TRaw K V) (Except ε) Unit) (get st).inner.1 = .ok (a, raw') ∧
      (hmInsertD get set k v : StateT σ (Except ε) Unit) st = .ok (a, st') ∧
      tabs st' = (tabs st).set i ⟨K, V, BI, raw'⟩ ∧ ∀ v, P st' v ↔ P st v := by
  intro st
  refine ⟨_, _, _, insertM_eq ⟨(get st).inner.1, (get st).inner.2.size_buckets_pos⟩ k v, rfl, ?_, hP st _⟩
  rw [htabs]
  rfl

theorem sim_clear {set : σ → Std.HashMap K V → σ}
    (htabs : ∀ st m, tabs (set st m) = (tabs st).set i ⟨K, V, BI, m.inner.1⟩)
    (hP : ∀ st m v, P (set st m) v ↔ P st v) :
    ∀ st, ∃ a raw' st', (emptyM : StateT (TRaw K V) (Except ε) Unit) (get st).inner.1 = .ok (a, raw') ∧
      (hmClear get set : StateT σ (Except ε) Unit) st = .ok (a, st') ∧
      tabs st' = (tabs st).set i ⟨K, V, BI, raw'⟩ ∧ ∀ v, P st' v ↔ P st v := by
  intro st
  refine ⟨_, _, _, emptyM_eq _, rfl, ?_, hP st _⟩
  rw [htabs]
  rfl

/-- The empty map's raw map, as `initRec` allocates it. -/
theorem emptyRaw_empty : EmptyRaw (∅ : Std.HashMap K V).inner.1 := by
  have := emptyM_eq (K := K) (V := V) (ε := Empty) (⟨0, #[]⟩ : TRaw K V)
  simp only [emptyM, tRealloc, tSetSize, bind, StateT.bind, Except.bind, Except.ok.injEq,
    Prod.mk.injEq, true_and] at this
  refine ⟨?_, ?_⟩
  · show (Raw₀.emptyWithCapacity (α := K) (β := fun _ => V) 8).1.size = 0
    rw [← this]
  · show (Raw₀.emptyWithCapacity (α := K) (β := fun _ => V) 8).1.buckets = _
    rw [← this]

end

/-! ## The runner's hypotheses, entry by entry -/

theorem emptyRaws_nil : ∀ e ∈ ([] : List TEntry), EmptyRaw e.raw := fun _ h => absurd h List.not_mem_nil

theorem emptyRaws_cons {e : TEntry} {l : List TEntry} (h₁ : EmptyRaw e.raw) (h₂ : ∀ x ∈ l, EmptyRaw x.raw) :
    ∀ x ∈ e :: l, EmptyRaw x.raw := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁
  · exact h₂ x hx

theorem f2_length {α : Type u} {β : Type v} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.length = l₂.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [f2_length h]

theorem f2_get {α : Type u} {β : Type v} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ k (h₁ : k < l₁.length) (h₂ : k < l₂.length),
      R l₁[k] l₂[k]
  | _ :: _, _ :: _, .cons hr _, 0, _, _ => hr
  | _ :: _, _ :: _, .cons _ h, k + 1, h₁, h₂ => f2_get h k (by simpa using h₁) (by simpa using h₂)

theorem initRec_ok' {σ : Type} {tabs : σ → List TEntry} {P : σ → Value → Prop} {env : SemEnv Value}
    {st a : VarN} {epv : Exp} {enils : List Exp} {init : σ}
    (hraw : ∀ e ∈ tabs init, EmptyRaw e.raw)
    (hnil : List.Forall₂ (fun e t => ∀ ns, Eval { env with v := ns } e (t.BI .nil)) enils (tabs init))
    (hpv : Eval env epv (P init)) :
    ∀ (τ : Type) (s : State τ), ∃ extra b loc,
      Runs s env [initRec st a epv enils] { s with refs := s.refs ++ extra } (.val [.loc b loc]) ∧
      (recRel tabs P loc).rel init (s.refs ++ extra) ∧
      ∀ l, (recRel tabs P loc).owns (s.refs ++ extra) l → s.refs.length ≤ l := by
  have hlen := f2_length hnil
  refine initRec_ok hlen (fun k hk => ?_) (fun k hk ns => ?_) hpv
  · exact hraw _ (List.getElem_mem hk)
  · exact f2_get hnil k hk (by omega) ns

end ConPastel.Translator
