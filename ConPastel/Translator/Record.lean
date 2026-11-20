import ConPastel.Translator.HashMapM

/-!
# A state record of hash tables

A state `σ` whose hash maps are held as tables updated in place
(`ConPastel.Translator.Table`), and whose other parts are plain values. The
state's cell `loc` is a CakeML array: the tables' handles (their cells), then
one value for the plain part.

`tabs st` lists the state's raw maps, with their bucket representations
(`TEntry`); `P st v` relates the plain part to its value. The relation
`recRel tabs P loc` owns the state's cell and every table's cells; the tables'
cells are pairwise disjoint and distinct from the state's cell.

`EvalM_lens`: a table operation (`EvalM` over `tblRel`) run on one field's
table is the operation on the state that changes that field's raw map alone.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL

/-- One table of the state: its raw map and the representation of its buckets. -/
structure TEntry where
  K : Type
  V : Type
  BI : RefInv (Bkt K V)
  raw : TRaw K V

/-- The cells owned by the table whose handle is `v` (`tblRel`'s ownership). -/
def tblOwns (r : Store Value) (v : Value) (l : Nat) : Prop :=
  ∃ b tl, v = .loc b tl ∧ (l = tl ∨ ∃ b' n, r[tl]? = some (.varray [.loc b' l, .litv (.intLit n)]))

theorem tblOwns_loc {K V : Type} {BI : RefInv (Bkt K V)} {r : Store Value} {b : Bool} {tl l : Nat} :
    tblOwns r (.loc b tl) l ↔ (tblRel BI tl).owns r l := by
  constructor
  · rintro ⟨b', tl', he, h⟩
    simp only [Value.loc.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact h
  · intro h
    exact ⟨b, tl, rfl, h⟩

/-- Ownership by a table reads only the table's cell. -/
theorem tblOwns_congr {r r' : Store Value} {b : Bool} {tl l : Nat} (h : r'[tl]? = r[tl]?) :
    tblOwns r' (.loc b tl) l ↔ tblOwns r (.loc b tl) l := by
  constructor
  · rintro ⟨b₁, tl₁, he, h₁⟩
    simp only [Value.loc.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨_, _, rfl, ?_⟩
    rcases h₁ with h₁ | ⟨b', n, hc⟩
    · exact Or.inl h₁
    · exact Or.inr ⟨b', n, by rw [← h, hc]⟩
  · rintro ⟨b₁, tl₁, he, h₁⟩
    simp only [Value.loc.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨_, _, rfl, ?_⟩
    rcases h₁ with h₁ | ⟨b', n, hc⟩
    · exact Or.inl h₁
    · exact Or.inr ⟨b', n, by rw [h, hc]⟩

/-- The tables' part of the relation, on the handle values `vals`. -/
structure RecOk {σ : Type} (tabs : σ → List TEntry) (P : σ → Value → Prop) (loc : Nat) (st : σ)
    (r : Store Value) (vals : List Value) : Prop where
  cell : r[loc]? = some (.varray vals)
  len : vals.length = (tabs st).length + 1
  plain : P st (vals[(tabs st).length]'(by omega))
  tbl : ∀ i (hi : i < (tabs st).length), ∃ b tl, vals[i]'(by omega) = .loc b tl ∧
    (tblRel ((tabs st)[i]).BI tl).rel ((tabs st)[i]).raw r
  disj : ∀ i j (hi : i < (tabs st).length) (hj : j < (tabs st).length), i ≠ j →
    ∀ l, tblOwns r (vals[i]'(by omega)) l → ¬ tblOwns r (vals[j]'(by omega)) l
  noLoc : ∀ i (hi : i < (tabs st).length), ¬ tblOwns r (vals[i]'(by omega)) loc

/-- The state record of tables. -/
def recRel {σ : Type} (tabs : σ → List TEntry) (P : σ → Value → Prop) (loc : Nat) : StateRel σ where
  owns r l := l = loc ∨ ∃ vals, r[loc]? = some (.varray vals) ∧
    ∃ i, ∃ hi : i + 1 < vals.length, tblOwns r (vals[i]'(by omega)) l
  rel st r := ∃ vals, RecOk tabs P loc st r vals
  inRange st r h l hl := by
    obtain ⟨vals, hk⟩ := h
    rcases hl with rfl | ⟨vals', hc, i, hi, ho⟩
    · exact (List.getElem?_eq_some_iff.mp hk.cell).1
    · rw [hk.cell] at hc
      simp only [Option.some.injEq, StoreValue.varray.injEq] at hc
      subst hc
      have hi' : i < (tabs st).length := by have := hk.len; omega
      obtain ⟨b, tl, hv, ht⟩ := hk.tbl i hi'
      rw [hv] at ho
      exact (tblRel _ tl).inRange _ r ht l (tblOwns_loc.mp ho)
  stable st r r' h _ hsame := by
    obtain ⟨vals, hk⟩ := h
    have hcell : r'[loc]? = r[loc]? := hsame loc (Or.inl rfl)
    have hown : ∀ i (hi : i + 1 < vals.length) l, tblOwns r (vals[i]'(by omega)) l → r'[l]? = r[l]? :=
      fun i hi l ho => hsame l (Or.inr ⟨vals, hk.cell, i, hi, ho⟩)
    -- each table's cell is the same, so its ownership is the same
    have hcongr : ∀ i (hi : i < (tabs st).length) l,
        tblOwns r' (vals[i]'(by have := hk.len; omega)) l ↔ tblOwns r (vals[i]'(by have := hk.len; omega)) l := by
      intro i hi l
      obtain ⟨b, tl, hv, ht⟩ := hk.tbl i hi
      rw [hv]
      apply tblOwns_congr
      exact hown i (by have := hk.len; omega) tl (by rw [hv]; exact ⟨b, tl, rfl, Or.inl rfl⟩)
    refine ⟨vals, ⟨by rw [hcell, hk.cell], hk.len, hk.plain, fun i hi => ?_, fun i j hi hj hij l ho₁ ho₂ => ?_,
      fun i hi ho => ?_⟩⟩
    · obtain ⟨b, tl, hv, ht⟩ := hk.tbl i hi
      refine ⟨b, tl, hv, (tblRel _ tl).stable _ r r' ht (by assumption) fun l ho => ?_⟩
      exact hown i (by have := hk.len; omega) l (by rw [hv]; exact tblOwns_loc.mpr ho)
    · exact hk.disj i j hi hj hij l ((hcongr i hi l).mp ho₁) ((hcongr j hj l).mp ho₂)
    · exact hk.noLoc i hi ((hcongr i hi loc).mp ho)
  ownsStable st r r' h _ hsame l _ ho := by
    obtain ⟨vals, hk⟩ := h
    have hcell : r'[loc]? = r[loc]? := hsame loc (Or.inl rfl)
    rcases ho with rfl | ⟨vals', hc, i, hi, ho⟩
    · exact Or.inl rfl
    · rw [hcell, hk.cell] at hc
      simp only [Option.some.injEq, StoreValue.varray.injEq] at hc
      subst hc
      have hi' : i < (tabs st).length := by have := hk.len; omega
      obtain ⟨b, tl, hv, ht⟩ := hk.tbl i hi'
      refine Or.inr ⟨_, hk.cell, i, hi, ?_⟩
      have htl : r'[tl]? = r[tl]? :=
        hsame tl (Or.inr ⟨_, hk.cell, i, hi, (by rw [hv]; exact ⟨b, tl, rfl, Or.inl rfl⟩)⟩)
      rw [hv] at ho ⊢
      exact (tblOwns_congr htl).mp ho

/-! ## Changing one table -/

theorem RecOk.tblOwns_lt {σ : Type} {tabs : σ → List TEntry} {P : σ → Value → Prop} {loc : Nat}
    {st : σ} {r : Store Value} {vals : List Value} (hk : RecOk tabs P loc st r vals) {j : Nat}
    (hj : j < (tabs st).length) {l : Nat} (ho : tblOwns r (vals[j]'(by have := hk.len; omega)) l) :
    l < r.length := by
  obtain ⟨b, tl, hv, ht⟩ := hk.tbl j hj
  rw [hv] at ho
  exact (tblRel _ tl).inRange _ r ht l (tblOwns_loc.mp ho)

/-- Table `i`'s cells change (`Frame` of `tblRel`) and it now holds `raw'`; the
state is `st'`, whose tables are `st`'s with table `i` replaced. -/
theorem RecOk.update {σ : Type} {tabs : σ → List TEntry} {P : σ → Value → Prop} {loc : Nat}
    {st st' : σ} {r r' : Store Value} {vals : List Value} (hk : RecOk tabs P loc st r vals)
    {i : Nat} (hi : i < (tabs st).length) {b : Bool} {tl : Nat}
    (hv : vals[i]'(by have := hk.len; omega) = .loc b tl) {K V : Type} {BI : RefInv (Bkt K V)}
    {raw' : TRaw K V} (hfr : Frame (tblRel BI tl) r r') (hrel : (tblRel BI tl).rel raw' r')
    (htabs : tabs st' = (tabs st).set i ⟨K, V, BI, raw'⟩) (hP : ∀ v, P st' v ↔ P st v) :
    RecOk tabs P loc st' r' vals ∧ Frame (recRel tabs P loc) r r' := by
  have hlen' : (tabs st').length = (tabs st).length := by rw [htabs, List.length_set]
  have hvl := hk.len
  -- cells table `i` did not own are unchanged
  have hsame : ∀ l, l < r.length → ¬ tblOwns r (.loc b tl) l → r'[l]? = r[l]? :=
    fun l hl hn => hfr.2.1 l hl (fun ho => hn (tblOwns_loc.mpr ho))
  -- the other tables' cells and the state's cell are not table `i`'s
  have hloc : r'[loc]? = r[loc]? := by
    refine hsame loc (List.getElem?_eq_some_iff.mp hk.cell).1 ?_
    have := hk.noLoc i hi; rwa [hv] at this
  have hother : ∀ j (hj : j < (tabs st).length), j ≠ i → ∀ l,
      tblOwns r' (vals[j]'(by omega)) l ↔ tblOwns r (vals[j]'(by omega)) l := by
    intro j hj hji l
    obtain ⟨bj, tlj, hvj, _⟩ := hk.tbl j hj
    rw [hvj]
    apply tblOwns_congr
    refine hsame tlj (hk.tblOwns_lt hj (by rw [hvj]; exact ⟨bj, tlj, rfl, Or.inl rfl⟩)) ?_
    have := hk.disj j i hj hi hji tlj (by rw [hvj]; exact ⟨bj, tlj, rfl, Or.inl rfl⟩)
    rwa [hv] at this
  -- table `i`'s cells now: old ones it owned, or new ones
  have hnew : ∀ l, tblOwns r' (.loc b tl) l → l < r.length → tblOwns r (.loc b tl) l :=
    fun l ho hl => tblOwns_loc.mpr (hfr.2.2 l hl (tblOwns_loc.mp ho))
  have hentj : ∀ j (hj : j < (tabs st').length), j ≠ i →
      (tabs st')[j] = (tabs st)[j]'(by omega) := by
    intro j hj hji
    simp [htabs, List.getElem_set, Ne.symm hji]
  have henti : (tabs st')[i]'(by omega) = ⟨K, V, BI, raw'⟩ := by
    simp [htabs, List.getElem_set]
  refine ⟨⟨by rw [hloc, hk.cell], by omega, ?_, fun j hj => ?_, fun j₁ j₂ hj₁ hj₂ hne l ho₁ ho₂ => ?_,
    fun j hj ho => ?_⟩, ⟨hfr.1, fun l hl hn => ?_, fun l hl ho => ?_⟩⟩
  · -- the plain part
    have hp := hk.plain
    have : vals[(tabs st').length]'(by omega) = vals[(tabs st).length]'(by omega) := by
      simp only [hlen']
    rw [this]; exact (hP _).mpr hp
  · -- each table
    by_cases hji : j = i
    · subst hji
      refine ⟨b, tl, hv, ?_⟩
      rw [henti]; exact hrel
    · have hj' : j < (tabs st).length := by omega
      obtain ⟨bj, tlj, hvj, htj⟩ := hk.tbl j hj'
      refine ⟨bj, tlj, hvj, ?_⟩
      rw [hentj j hj hji]
      refine (tblRel _ tlj).stable _ r r' htj hfr.1 fun l ho => ?_
      refine hsame l ((tblRel _ tlj).inRange _ r htj l ho) ?_
      have := hk.disj j i hj' hi hji l (by rw [hvj]; exact tblOwns_loc.mpr ho)
      rwa [hv] at this
  · -- disjoint
    have hj₁' : j₁ < (tabs st).length := by omega
    have hj₂' : j₂ < (tabs st).length := by omega
    -- move both ownerships back to the old store
    have back : ∀ j (hj : j < (tabs st).length) l, tblOwns r' (vals[j]'(by omega)) l →
        l < r.length → tblOwns r (vals[j]'(by omega)) l := by
      intro j hj l ho hl
      by_cases hji : j = i
      · subst hji; rw [hv] at ho ⊢; exact hnew l ho hl
      · exact (hother j hj hji l).mp ho
    have lt : ∀ j (hj : j < (tabs st).length) l, tblOwns r' (vals[j]'(by omega)) l → j ≠ i → l < r.length := by
      intro j hj l ho hji
      exact hk.tblOwns_lt hj ((hother j hj hji l).mp ho)
    by_cases hl : l < r.length
    · exact hk.disj j₁ j₂ hj₁' hj₂' hne l (back j₁ hj₁' l ho₁ hl) (back j₂ hj₂' l ho₂ hl)
    · -- a new cell: only table `i` can own it
      by_cases h₁ : j₁ = i
      · exact hl (lt j₂ hj₂' l ho₂ (by omega))
      · exact hl (lt j₁ hj₁' l ho₁ h₁)
  · -- not the state's cell
    have hj' : j < (tabs st).length := by omega
    have hlocr : loc < r.length := (List.getElem?_eq_some_iff.mp hk.cell).1
    by_cases hji : j = i
    · subst hji; rw [hv] at ho
      have := hk.noLoc j hj'; rw [hv] at this
      exact this (hnew loc ho hlocr)
    · exact hk.noLoc j hj' ((hother j hj' hji loc).mp ho)
  · -- unowned cells unchanged
    exact hsame l hl fun ho => hn (Or.inr ⟨vals, hk.cell, i, by omega, by rw [hv]; exact ho⟩)
  · -- owned cells were owned
    rcases ho with rfl | ⟨vals', hc, j, hj, ho⟩
    · exact Or.inl rfl
    · rw [hloc, hk.cell] at hc
      simp only [Option.some.injEq, StoreValue.varray.injEq] at hc
      subst hc
      have hj' : j < (tabs st).length := by omega
      refine Or.inr ⟨_, hk.cell, j, hj, ?_⟩
      by_cases hji : j = i
      · subst hji; rw [hv] at ho ⊢; exact hnew l ho hl
      · exact (hother j hj' hji l).mp ho

/-- The handle of table `i`: `Array.sub h i`. -/
abbrev handleAt (h : VarN) (i : Nat) : Exp := .app .asub [.var (.short h), .lit (.intLit ((i : Nat) : Int))]

/-- **A table operation on one field.** -/
theorem EvalM_lens {σ ε α : Type} {tabs : σ → List TEntry} {P : σ → Value → Prop} {loc : Nat}
    {env : SemEnv Value} {h : VarN} {b₀ : Bool} {i : Nat} {K V : Type} {BI : RefInv (Bkt K V)}
    {getR : σ → TRaw K V} {ef : Exp} {A : RefInv α} {B : RefInv ε}
    {mT : StateT (TRaw K V) (Except ε) α} {mC : StateT σ (Except ε) α}
    (hh : nsLookup env.v (.short h) = some (.loc b₀ loc))
    (hlen : ∀ st, i < (tabs st).length)
    (hent : ∀ st, (tabs st)[i]'(hlen st) = ⟨K, V, BI, getR st⟩)
    (hf : Eval env ef (MRET (tblRel BI) A B mT))
    (hsim : ∀ st, ∃ a raw' st', mT (getR st) = .ok (a, raw') ∧ mC st = .ok (a, st') ∧
        tabs st' = (tabs st).set i ⟨K, V, BI, raw'⟩ ∧ ∀ v, P st' v ↔ P st v) :
    EvalM (recRel tabs P loc) env (.app .opapp [ef, handleAt h i]) A B mC := by
  intro τ s st hst
  obtain ⟨vals, hk⟩ := hst
  have hi := hlen st
  have hvl := hk.len
  obtain ⟨b, tl, hv, ht⟩ := hk.tbl i hi
  have ht' : (tblRel BI tl).rel (getR st) s.refs := by
    have := ht; rw [hent st] at this; exact this
  obtain ⟨vf, extra, hfr, hM⟩ := hf τ s
  have hargs : Runs s env [handleAt h i, ef] { s with refs := s.refs ++ extra } (.val [.loc b tl, vf]) := by
    obtain ⟨c₁, c₂, hc⟩ := hfr.runs
    refine ⟨c₁, c₂, ?_⟩
    have ha := evaluate_asub_lit { s with clock := c₁ } hh (by simpa using hk.cell) (k := i) (by omega)
    rw [hv] at ha
    exact evaluate_cons_val ha hc
  have hrel₁ := StateRel.rel_append ht' extra
  obtain ⟨env', body, happ, refs', res, hrun, hfm, hm⟩ :=
    hM τ { s with refs := s.refs ++ extra } (getR st) b tl hrel₁
  obtain ⟨a, raw', st', hmT, hmC, htabs, hP⟩ := hsim st
  rw [hmT] at hm
  obtain ⟨hrel', v, hres, hA⟩ := hm
  subst hres
  have hk₁ : RecOk tabs P loc st (s.refs ++ extra) vals := by
    obtain ⟨vals₁, hk₁⟩ := StateRel.rel_append (R := recRel tabs P loc) ⟨vals, hk⟩ extra
    have : vals₁ = vals := by
      have h1 := hk₁.cell
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk.cell).1, hk.cell] at h1
      simp only [Option.some.injEq, StoreValue.varray.injEq] at h1
      exact h1.symm
    subst this; exact hk₁
  obtain ⟨hk', hframe⟩ := hk₁.update hi hv hfm hrel' htabs hP
  refine ⟨refs', .val [v], ?_, (Frame.append (R := recRel tabs P loc) ⟨vals, hk⟩ extra).trans hframe, ?_⟩
  · exact Runs.app_opapp_any hargs happ (by simpa using hrun) (by simp)
  · rw [hmC]
    exact ⟨⟨vals, hk'⟩, v, rfl, hA⟩

/-! ## Running a computation on a freshly initialized state -/

/-- Run `m` from `init` on a state that the code `ei` allocates: `ei` runs to a
handle whose relation holds of `init`, owning only fresh cells. As
`Eval_runRef`, the result (or, by `handle`, the exception) is pure. -/
theorem Eval_runState {σ ε α β : Type} {RF : Nat → StateRel σ} {A : RefInv α} {B : RefInv ε}
    {P : RefInv β} {env : SemEnv Value} {ei em eok eerr : Exp} {h x y : VarN} {init : σ}
    {m : StateT σ (Except ε) α} {ok : α → β} {err : ε → β}
    (hi : ∀ (τ : Type) (s : State τ), ∃ extra b loc,
      Runs s env [ei] { s with refs := s.refs ++ extra } (.val [.loc b loc]) ∧
      (RF loc).rel init (s.refs ++ extra) ∧ ∀ l, (RF loc).owns (s.refs ++ extra) l → s.refs.length ≤ l)
    (hm : ∀ b loc, Eval { env with v := nsOptBind (some h) (.loc b loc) env.v } em (MRET RF A B m))
    (hok : ∀ b loc a v, A a v →
      Eval { env with v := nsOptBind (some x) v (nsOptBind (some h) (.loc b loc) env.v) } eok (P (ok a)))
    (herr : ∀ b loc e v, B e v →
      Eval { env with v := nsAppend (alistToNs [(y, v)]) (nsOptBind (some h) (.loc b loc) env.v) } eerr
        (P (err e))) :
    Eval env (.let_ (some h) ei
      (.handle (.let_ (some x) (.app .opapp [em, .var (.short h)]) eok) [(.pvar y, eerr)]))
      (P (match m init with | .ok (a, _) => ok a | .error e => err e)) := by
  intro τ s
  obtain ⟨extra, b, loc, hrun₀, hst, hfresh⟩ := hi τ s
  let s₂ : State τ := { s with refs := s.refs ++ extra }
  let env₁ : SemEnv Value := { env with v := nsOptBind (some h) (.loc b loc) env.v }
  have hrun := EvalM_run (RF := RF) (env := env₁) (h := .short h) (b := b) (loc := loc)
    (by simp [env₁, nsOptBind, nsLookup_nsBind_short]) (hm b loc)
  obtain ⟨refs', res, hr, hfr, hres⟩ := hrun τ s₂ init hst
  have hpre : ∀ l < s.refs.length, refs'[l]? = s₂.refs[l]? := fun l hl =>
    hfr.2.1 l (by simp [s₂]; omega) (fun ho => by have := hfresh l ho; omega)
  have hext : refs' = s.refs ++ refs'.drop s.refs.length := by
    apply List.ext_getElem?
    intro l
    by_cases hl : l < s.refs.length
    · rw [List.getElem?_append_left (by simpa using hl), hpre l hl]
      simp [s₂, List.getElem?_append_left hl]
    · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
      congr 1; omega
  revert hres
  cases hm' : m init with
  | ok p =>
    obtain ⟨a, st'⟩ := p
    intro hres
    obtain ⟨_, v, hv, hA⟩ := hres
    subst hv
    obtain ⟨w, extra₂, hw, hP⟩ := hok b loc a v hA τ { s with refs := refs' }
    refine ⟨w, refs'.drop s.refs.length ++ extra₂, ?_, hP⟩
    apply Runs.evalRel
    have hlet := Runs.let_ (n := some x) (env := env₁) hr (by simpa using hw.runs) (by simp)
    have hh := Runs.handle_val (cls := [(.pvar y, eerr)]) hlet
    have := Runs.let_ (n := some h) (env := env) hrun₀ (by simpa [s₂, env₁] using hh) (by simp)
    rw [hext] at this
    simpa [List.append_assoc] using this
  | error e =>
    intro hres
    obtain ⟨v, hv, hB⟩ := hres
    subst hv
    obtain ⟨w, extra₂, hw, hP⟩ := herr b loc e v hB τ { s with refs := refs' }
    refine ⟨w, refs'.drop s.refs.length ++ extra₂, ?_, hP⟩
    apply Runs.evalRel
    have hlet := Runs.let_err (n := some x) (e₂ := eok) (env := env₁) hr
    have hh := Runs.handle_raise (x := y) (rhs := eerr) hlet (by simpa [env₁] using hw.runs) (by simp)
    have := Runs.let_ (n := some h) (env := env) hrun₀ (by simpa [s₂, env₁] using hh) (by simp)
    rw [hext] at this
    simpa [List.append_assoc] using this

/-! ## Allocating the state record -/

/-- An empty table: `let a = Array.array 16 nil in Array.fromList [a, 0]`. -/
def newTbl (a : VarN) (enil : Exp) : Exp :=
  .let_ (some a) (.app .aalloc [.lit (.intLit ((16 : Nat) : Int)), enil])
    (.app .aallocFixed [.var (.short a), .lit (.intLit ((0 : Nat) : Int))])

/-- The raw map of `emptyWithCapacity 8`. -/
def EmptyRaw {K V : Type} (raw : TRaw K V) : Prop := raw.size = 0 ∧ raw.buckets = Array.replicate 16 .nil

theorem Runs_newTbl {τ : Type} {s : State τ} {env : SemEnv Value} {a : VarN} {enil : Exp}
    {K V : Type} {BI : RefInv (Bkt K V)} (he : Eval env enil (BI .nil)) :
    ∃ extra vn, Runs s env [newTbl a enil]
      { s with refs := s.refs ++ extra ++ [.varray (List.replicate 16 vn),
        .varray [.loc true (s.refs.length + extra.length), .litv (.intLit 0)]] }
      (.val [.loc true (s.refs.length + extra.length + 1)]) ∧ BI .nil vn := by
  obtain ⟨vn, extra, hv, hB⟩ := he τ s
  refine ⟨extra, vn, ?_, hB⟩
  let s₁ : State τ := { s with refs := s.refs ++ extra }
  have hargs : Runs s env [enil, .lit (.intLit ((16 : Nat) : Int))] s₁ (.val [vn, .litv (.intLit 16)]) := by
    obtain ⟨c₁, c₂, hc⟩ := hv.runs
    exact ⟨c₁, c₂, evaluate_cons_val hc (by simp only [evaluate]; rfl)⟩
  have halloc := Runs.aalloc hargs
  let s₂ : State τ := { s₁ with refs := s₁.refs ++ [.varray (List.replicate 16 vn)] }
  let env₁ : SemEnv Value := { env with v := nsOptBind (some a) (.loc true s₁.refs.length) env.v }
  have hfix : Runs s₂ env₁ [.app .aallocFixed [.var (.short a), .lit (.intLit ((0 : Nat) : Int))]]
      { s₂ with refs := s₂.refs ++ [.varray [.loc true s₁.refs.length, .litv (.intLit 0)]] }
      (.val [.loc true s₂.refs.length]) := by
    refine ⟨0, 0, ?_⟩
    have hargs₂ : evaluate { s₂ with clock := 0 } env₁ [.lit (.intLit ((0 : Nat) : Int)), .var (.short a)] =
        ({ s₂ with clock := 0 }, .val [.litv (.intLit 0), .loc true s₁.refs.length]) :=
      evaluate_cons_val (s₁ := { s₂ with clock := 0 }) (by simp [evaluate]) (by simp [evaluate, env₁, nsl_self])
    have := evaluate_app_simple (s := { s₂ with clock := 0 }) (s₁ := { s₂ with clock := 0 }) (env := env₁)
      (op := .aallocFixed) (args := [.var (.short a), .lit (.intLit ((0 : Nat) : Int))])
      (vs := [.litv (.intLit 0), .loc true s₁.refs.length])
      (refs := s₂.refs ++ [.varray [.loc true s₁.refs.length, .litv (.intLit 0)]]) (ffi := s₂.ffi)
      (r := .val (.loc true s₂.refs.length)) (by simpa using hargs₂) rfl
      (by simp [doApp, doAppBasic, doAppNumericCore, storeAlloc])
    simpa [listResult] using this
  have := Runs.let_ (n := some a) halloc hfix (by simp)
  simpa [s₂, s₁, newTbl, List.append_assoc, Nat.add_assoc] using this

/-- Fill the table handles `i, i + 1, …` of the state array `st` with new tables. -/
def fillTbls (st a : VarN) : Nat → List Exp → Exp
  | _, [] => .var (.short st)
  | i, e :: es => .let_ none (.app .aupdate [.var (.short st), .lit (.intLit ((i : Nat) : Int)), newTbl a e])
      (fillTbls st a (i + 1) es)

/-- The state record: an array of `n + 1` copies of the plain part, then a new
table at each handle. -/
def initRec (st a : VarN) (epv : Exp) (enils : List Exp) : Exp :=
  .let_ (some st) (.app .aalloc [.lit (.intLit ((enils.length + 1 : Nat) : Int)), epv])
    (fillTbls st a 0 enils)

theorem forall₂_replicate' {α : Type} {A : RefInv α} {x : α} {vx : Value} (hx : A x vx) (n : Nat) :
    List.Forall₂ A (Array.replicate n x).toList (List.replicate n vx) := by
  simpa using forall₂_replicate hx n

/-- The new table's relation. -/
theorem newTbl_rel {K V : Type} {BI : RefInv (Bkt K V)} {r : Store Value} {vn : Value} (hB : BI .nil vn)
    {A T : Nat} (hA : r[A]? = some (.varray (List.replicate 16 vn)))
    (hT : r[T]? = some (.varray [.loc true A, .litv (.intLit 0)])) (hne : A ≠ T)
    (raw : TRaw K V) (hraw : EmptyRaw raw) : (tblRel BI T).rel raw r := by
  obtain ⟨hs, hb⟩ := hraw
  refine ⟨true, A, List.replicate 16 vn, by rw [hs]; simpa using hT, hne, hA, ?_⟩
  rw [hb]; exact forall₂_replicate' hB 16

/-- What filling the handles produces. -/
structure FillOk {τ : Type} (s : State τ) (L : Nat) (hs : List Value) (pvv : Value) (ents : List TEntry)
    (refs' : Store Value) (hs' : List Value) : Prop where
  len : s.refs.length ≤ refs'.length
  cell : refs'[L]? = some (.varray (hs ++ hs' ++ [pvv]))
  hlen : hs'.length = ents.length
  same : ∀ l < s.refs.length, l ≠ L → refs'[l]? = s.refs[l]?
  tbl : ∀ k (hk : k < ents.length), ∃ tl, hs'[k]'(by omega) = .loc true tl ∧
    ∀ raw : TRaw (ents[k]).K (ents[k]).V, EmptyRaw raw → (tblRel (ents[k]).BI tl).rel raw refs'
  fresh : ∀ k (hk : k < ents.length) l, tblOwns refs' (hs'[k]'(by omega)) l → s.refs.length ≤ l ∧ l ≠ L
  disj : ∀ k₁ k₂ (h₁ : k₁ < ents.length) (h₂ : k₂ < ents.length), k₁ ≠ k₂ → ∀ l,
    tblOwns refs' (hs'[k₁]'(by omega)) l → ¬ tblOwns refs' (hs'[k₂]'(by omega)) l

theorem tblOwns_new {r : Store Value} {A T l : Nat}
    (hT : r[T]? = some (.varray [.loc true A, .litv (.intLit 0)])) (ho : tblOwns r (.loc true T) l) :
    l = T ∨ l = A := by
  obtain ⟨b, tl, he, h⟩ := ho
  simp only [Value.loc.injEq] at he
  obtain ⟨-, rfl⟩ := he
  rcases h with h | ⟨b', n, hc⟩
  · exact Or.inl h
  · rw [hT] at hc
    simp only [Option.some.injEq, StoreValue.varray.injEq, List.cons.injEq, Value.loc.injEq] at hc
    exact Or.inr hc.1.2.symm

theorem Runs_fill {τ : Type} (st a : VarN) {env : SemEnv Value} {L : Nat} {pvv : Value}
    (hst : nsLookup env.v (.short st) = some (.loc true L)) :
    ∀ (es : List Exp) (ents : List TEntry) (i : Nat) (s : State τ) (hs : List Value)
    (_ : es.length = ents.length) (_ : hs.length = i)
    (_ : ∀ k (hk : k < es.length) ns, Eval { env with v := ns } (es[k]) ((ents[k]'(by omega)).BI .nil)),
    s.refs[L]? = some (.varray (hs ++ List.replicate (es.length + 1) pvv)) →
    ∃ refs' hs', Runs s env [fillTbls st a i es] { s with refs := refs' } (.val [.loc true L]) ∧
      FillOk s L hs pvv ents refs' hs'
  | [], ents, i, s, hs, hl, _, _, hc => by
    have : ents = [] := by
      cases ents with
      | nil => rfl
      | cons _ _ => exact absurd hl (by simp)
    subst this
    refine ⟨s.refs, [], ⟨0, 0, by simp [fillTbls, evaluate, hst]⟩,
      ⟨Nat.le_refl _, by simpa using hc, rfl, fun _ _ _ => rfl, fun k hk => by simp at hk,
        fun k hk => by simp at hk, fun k _ hk => by simp at hk⟩⟩
  | e :: es, ents, i, s, hs, hl, hi, hnil, hc => by
    obtain ⟨ent, ents', rfl⟩ : ∃ ent ents', ents = ent :: ents' := by
      cases ents with
      | nil => simp at hl
      | cons x xs => exact ⟨x, xs, rfl⟩
    have hL : L < s.refs.length := (List.getElem?_eq_some_iff.mp hc).1
    -- the new table
    have he : Eval env e (ent.BI .nil) := by
      have := hnil 0 (by simp) env.v
      simpa using this
    obtain ⟨extra₁, vn, hrun₁, hB⟩ := Runs_newTbl (s := s) (a := a) he
    obtain ⟨A, hAd⟩ : ∃ A, A = s.refs.length + extra₁.length := ⟨_, rfl⟩
    obtain ⟨T, hTd⟩ : ∃ T, T = A + 1 := ⟨_, rfl⟩
    rw [← hAd] at hrun₁
    rw [← hTd] at hrun₁
    let r₁ := s.refs ++ extra₁ ++ [.varray (List.replicate 16 vn), .varray [.loc true A, .litv (.intLit 0)]]
    have hlen₁ : r₁.length = T + 1 := by simp [r₁]; omega
    have hA₁ : r₁[A]? = some (.varray (List.replicate 16 vn)) := by
      show ((s.refs ++ extra₁) ++ _)[A]? = _
      rw [hAd, ← List.length_append, List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hT₁ : r₁[T]? = some (.varray [.loc true A, .litv (.intLit 0)]) := by
      show ((s.refs ++ extra₁) ++ _)[T]? = _
      rw [hTd, hAd, ← List.length_append, List.getElem?_append_right (by omega)]
      simp
    have hL₁ : r₁[L]? = s.refs[L]? := by simp [r₁, List.append_assoc, List.getElem?_append_left hL]
    -- the handle written at index `i`
    let vals₁ := hs ++ List.replicate (es.length + 2) pvv
    have hi₁ : i < vals₁.length := by simp [vals₁]; omega
    let r₂ := r₁.set L (.varray (vals₁.set i (.loc true T)))
    have hupd : Runs s env [.app .aupdate [.var (.short st), .lit (.intLit ((i : Nat) : Int)), newTbl a e]]
        { s with refs := r₂ } (.val [.conv none []]) := by
      obtain ⟨c₁, c₂, hc₁⟩ := hrun₁
      refine ⟨c₁, c₂, ?_⟩
      have hargs : evaluate { s with clock := c₁ } env
          [newTbl a e, .lit (.intLit ((i : Nat) : Int)), .var (.short st)] =
          ({ s with clock := c₂, refs := r₁ }, .val [.loc true T, .litv (.intLit i), .loc true L]) := by
        refine evaluate_cons_val (s₁ := { s with clock := c₂, refs := r₁ }) ?_ ?_
        · simpa [r₁, List.append_assoc] using hc₁
        · exact evaluate_cons_val (s₁ := { s with clock := c₂, refs := r₁ }) (by simp [evaluate])
            (by simp [evaluate, hst])
      have := evaluate_app_simple (s := { s with clock := c₁ }) (s₁ := { s with clock := c₂, refs := r₁ })
        (env := env) (op := .aupdate) (args := [.var (.short st), .lit (.intLit ((i : Nat) : Int)), newTbl a e])
        (vs := [.loc true T, .litv (.intLit i), .loc true L]) (refs := r₂) (ffi := s.ffi)
        (r := .val (.conv none [])) (by simpa using hargs) rfl
        (by
          have hneg : ¬ ((i : Int) < 0) := by omega
          have hle : ¬ (vals₁.length ≤ i) := by omega
          have hcL : r₁[L]? = some (.varray vals₁) := by rw [hL₁, hc]; rfl
          simp [doApp, doAppBasic, doAppNumericCore, storeLookup, hcL, updateIndexed, hneg, hle,
            storeAssign, storeValueSameType, r₂])
      simpa [listResult] using this
    -- the rest
    have hvals : vals₁.set i (.loc true T) = (hs ++ [.loc true T]) ++ List.replicate (es.length + 1) pvv := by
      simp only [vals₁, ← hi]
      rw [List.set_append_right _ _ (by omega)]
      simp [List.replicate_succ]
    have hc₂ : r₂[L]? = some (.varray ((hs ++ [.loc true T]) ++ List.replicate (es.length + 1) pvv)) := by
      simp only [r₂]
      rw [List.getElem?_set_self (by simp [r₁]; omega), hvals]
    obtain ⟨refs', hs'', hrun₂, hok⟩ := Runs_fill st a hst es ents' (i + 1) { s with refs := r₂ }
      (hs ++ [.loc true T]) (by simpa using hl) (by simp [hi])
      (fun k hk ns => hnil (k + 1) (by simp; omega) ns) hc₂
    refine ⟨refs', .loc true T :: hs'', ?_, ?_⟩
    · have := Runs.let_ (n := none) hupd (by simpa [nsOptBind] using hrun₂) (by simp)
      simpa [fillTbls] using this
    · -- the facts, from the rest's and the new table's
      have hr₂len : r₂.length = T + 1 := by simp [r₂, hlen₁]
      have hA₂ : r₂[A]? = some (.varray (List.replicate 16 vn)) := by
        simp only [r₂]
        rw [List.getElem?_set_ne (by omega)]
        exact hA₁
      have hT₂ : r₂[T]? = some (.varray [.loc true A, .litv (.intLit 0)]) := by
        simp only [r₂]
        rw [List.getElem?_set_ne (by omega)]
        exact hT₁
      -- cells of `r₂` other than `L` are kept by the rest
      have hkeep : ∀ l < r₂.length, l ≠ L → refs'[l]? = r₂[l]? := hok.same
      have hA' : refs'[A]? = some (.varray (List.replicate 16 vn)) := by
        rw [hkeep A (by omega) (by omega), hA₂]
      have hT' : refs'[T]? = some (.varray [.loc true A, .litv (.intLit 0)]) := by
        rw [hkeep T (by omega) (by omega), hT₂]
      have hnewOwn : ∀ l, tblOwns refs' (.loc true T) l → l = T ∨ l = A := fun l ho => tblOwns_new hT' ho
      refine ⟨by have h1 := hok.len; dsimp only at h1; omega, by simpa using hok.cell, by simp [hok.hlen], ?_, ?_, ?_, ?_⟩
      · intro l hl hne
        rw [hkeep l (by omega) hne]
        simp only [r₂]
        rw [List.getElem?_set_ne (Ne.symm hne)]
        simp [r₁, List.append_assoc, List.getElem?_append_left hl]
      · intro k hk
        cases k with
        | zero =>
          refine ⟨T, rfl, fun raw hraw => ?_⟩
          exact newTbl_rel hB hA' hT' (by omega) raw hraw
        | succ k =>
          obtain ⟨tl, hv, htl⟩ := hok.tbl k (by simp at hk; omega)
          exact ⟨tl, by simpa using hv, by simpa using htl⟩
      · intro k hk l ho
        cases k with
        | zero =>
          rcases hnewOwn l (by simpa using ho) with rfl | rfl <;> constructor <;> omega
        | succ k =>
          have := hok.fresh k (by simp at hk; omega) l (by simpa using ho)
          dsimp only at this
          constructor <;> omega
      · intro k₁ k₂ h₁ h₂ hne l ho₁ ho₂
        cases k₁ with
        | zero =>
          cases k₂ with
          | zero => exact hne rfl
          | succ k₂ =>
            have := hok.fresh k₂ (by simp at h₂; omega) l (by simpa using ho₂)
            dsimp only at this
            rcases hnewOwn l (by simpa using ho₁) with rfl | rfl <;> omega
        | succ k₁ =>
          cases k₂ with
          | zero =>
            have := hok.fresh k₁ (by simp at h₁; omega) l (by simpa using ho₁)
            dsimp only at this
            rcases hnewOwn l (by simpa using ho₂) with rfl | rfl <;> omega
          | succ k₂ =>
            exact hok.disj k₁ k₂ (by simp at h₁; omega) (by simp at h₂; omega) (by omega) l
              (by simpa using ho₁) (by simpa using ho₂)

/-- **The record's initialization**: fresh, empty tables and the plain part. -/
theorem initRec_ok {σ : Type} {tabs : σ → List TEntry} {P : σ → Value → Prop} {env : SemEnv Value}
    {st a : VarN} {epv : Exp} {enils : List Exp} {init : σ}
    (hlen : enils.length = (tabs init).length)
    (hraw : ∀ k (hk : k < (tabs init).length), EmptyRaw ((tabs init)[k]).raw)
    (hnil : ∀ k (hk : k < enils.length) ns,
      Eval { env with v := ns } (enils[k]) (((tabs init)[k]'(by omega)).BI .nil))
    (hpv : Eval env epv (P init)) :
    ∀ (τ : Type) (s : State τ), ∃ extra b loc,
      Runs s env [initRec st a epv enils] { s with refs := s.refs ++ extra } (.val [.loc b loc]) ∧
      (recRel tabs P loc).rel init (s.refs ++ extra) ∧
      ∀ l, (recRel tabs P loc).owns (s.refs ++ extra) l → s.refs.length ≤ l := by
  intro τ s
  obtain ⟨pvv, extra₀, hv, hP⟩ := hpv τ s
  let s₀ : State τ := { s with refs := s.refs ++ extra₀ }
  have hargs : Runs s env [epv, .lit (.intLit ((enils.length + 1 : Nat) : Int))] s₀
      (.val [pvv, .litv (.intLit (enils.length + 1))]) := by
    obtain ⟨c₁, c₂, hc⟩ := hv.runs
    exact ⟨c₁, c₂, evaluate_cons_val hc (by simp only [evaluate]; rfl)⟩
  have halloc := Runs.aalloc hargs
  let L := s₀.refs.length
  let r₀ := s₀.refs ++ [.varray (List.replicate (enils.length + 1) pvv)]
  let env₁ : SemEnv Value := { env with v := nsOptBind (some st) (.loc true L) env.v }
  have hst : nsLookup env₁.v (.short st) = some (.loc true L) := nsl_self
  have hc₀ : r₀[L]? = some (.varray ([] ++ List.replicate (enils.length + 1) pvv)) := by simp [r₀, L]
  obtain ⟨refs', hs', hrun, hok⟩ := Runs_fill (env := env₁) st a hst enils (tabs init) 0
    { s with refs := r₀ } [] hlen rfl (fun k hk ns => hnil k hk ns) hc₀
  have hL : s.refs.length ≤ L := by simp [L, s₀]
  have hLlt : L < r₀.length := by simp [r₀, L]
  have hpre : ∀ l < s.refs.length, refs'[l]? = s.refs[l]? := by
    intro l hl
    rw [hok.same l (by simp [r₀, s₀]; omega) (by omega)]
    simp [r₀, s₀, List.append_assoc, List.getElem?_append_left hl]
  have hlen' : s.refs.length ≤ refs'.length := by have := hok.len; simp [r₀, s₀] at this; omega
  have hext : refs' = s.refs ++ refs'.drop s.refs.length := by
    apply List.ext_getElem?
    intro l
    by_cases hl : l < s.refs.length
    · rw [List.getElem?_append_left (by simpa using hl), hpre l hl]
    · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
      congr 1; omega
  have hn : hs'.length = (tabs init).length := hok.hlen
  refine ⟨refs'.drop s.refs.length, true, L, ?_, ?_, ?_⟩
  · have := Runs.let_ (n := some st) (env := env) (s₂ := { s with refs := refs' }) (r := .val [.loc true L])
      halloc hrun (by simp)
    rw [← hext]
    exact this
  · rw [← hext]
    refine ⟨hs' ++ [pvv], ⟨by simpa using hok.cell, by simp [hn], ?_, fun k hk => ?_,
      fun k₁ k₂ h₁ h₂ hne l ho₁ ho₂ => ?_, fun k hk ho => ?_⟩⟩
    · have : (hs' ++ [pvv])[(tabs init).length]'(by simp [hn]) = pvv := by
        rw [List.getElem_append_right (by omega)]; simp [hn]
      rw [this]; exact hP
    · obtain ⟨tl, hv', htl⟩ := hok.tbl k hk
      refine ⟨true, tl, ?_, htl _ (hraw k hk)⟩
      rw [List.getElem_append_left (by omega)]; exact hv'
    · rw [List.getElem_append_left (by omega)] at ho₁ ho₂
      exact hok.disj k₁ k₂ h₁ h₂ hne l ho₁ ho₂
    · rw [List.getElem_append_left (by omega)] at ho
      exact (hok.fresh k hk L ho).2 rfl
  · rw [← hext]
    rintro l (rfl | ⟨vals, hc, i, hi, ho⟩)
    · exact hL
    · rw [hok.cell] at hc
      simp only [Option.some.injEq, StoreValue.varray.injEq, List.nil_append] at hc
      subst hc
      have hi' : i < (tabs init).length := by simp at hi; omega
      rw [List.getElem_append_left (by omega)] at ho
      have := (hok.fresh i hi' l ho).1
      simp [r₀, s₀] at this; omega

/-! ## The plain part -/

/-- Reading the plain part: `Array.sub h n`. -/
theorem EvalM_plain {σ ε α : Type} {tabs : σ → List TEntry} {P : σ → Value → Prop} {loc : Nat}
    {env : SemEnv Value} {h : VarN} {b₀ : Bool} {n : Nat} {A : RefInv α} {B : RefInv ε} {f : σ → α}
    (hh : nsLookup env.v (.short h) = some (.loc b₀ loc)) (hlen : ∀ st, (tabs st).length = n)
    (hA : ∀ st v, P st v → A (f st) v) :
    EvalM (recRel tabs P loc) env (handleAt h n) A B (fun st => .ok (f st, st)) := by
  intro τ s st hst
  obtain ⟨vals, hk⟩ := hst
  have hvl := hk.len
  have hn : n < vals.length := by rw [← hlen st]; omega
  refine ⟨s.refs, .val [vals[n]], ⟨s.clock, s.clock, ?_⟩, Frame.refl _ _, ⟨vals, hk⟩, vals[n], rfl, ?_⟩
  · exact evaluate_asub_lit { s with clock := s.clock } hh hk.cell hn
  · have := hk.plain
    have he : vals[(tabs st).length]'(by omega) = vals[n] := by simp only [hlen st]
    rw [he] at this
    exact hA st _ this

end ConPastel.Translator
