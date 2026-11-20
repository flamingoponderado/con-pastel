import ConPastel.Translator.StateOps

/-!
# Swapping tables of a state record around a computation

con-leche runs its eager comparisons on a second set of memo maps
(`withEagerMemos`): the plain maps move out of the state, the eager ones move
into their fields, the eager fields become empty, and afterwards everything
moves back. On a state record (`recRel`) the maps are tables, so a move is a
write of a table's handle into another field. This file proves the code that
does it:

1. save the handles of the fields that move out (`readsExp`);
2. allocate fresh empty tables (`freshExp`);
3. write the handles into their new fields (`writesExp`);
4. run the computation;
5. write the handles back.

While the computation runs, the saved tables are referenced by no field: the
state does not own them, so the computation cannot change them (`Frame`).
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL

/-! ## Saving handles into variables -/

/-- `let s₁ = Array.sub h j₁ in … in k`. -/
def readsExp (h : VarN) : List (VarN × Nat) → Exp → Exp
  | [], k => k
  | (s, j) :: rs, k => .let_ (some s) (handleAt h j) (readsExp h rs k)

/-- The environment after `readsExp`. -/
def readsEnv (env : SemEnv Value) (vals : List Value) : List (VarN × Nat) → SemEnv Value
  | [] => env
  | (s, j) :: rs => readsEnv { env with v := nsOptBind (some s) (vals.getD j (.conv none [])) env.v } vals rs

theorem readsEnv_c (env : SemEnv Value) (vals : List Value) :
    ∀ rs, (readsEnv env vals rs).c = env.c
  | [] => rfl
  | (_, _) :: rs => by simp only [readsEnv]; rw [readsEnv_c _ _ rs]

theorem Runs_reads {τ : Type} {h : VarN} {loc : Nat} {b₀ : Bool} {vals : List Value} :
    ∀ (rs : List (VarN × Nat)) (env : SemEnv Value) (s s₂ : State τ) (k : Exp) (res : Result (List Value) Value),
    nsLookup env.v (.short h) = some (.loc b₀ loc) → s.refs[loc]? = some (.varray vals) →
    (∀ p ∈ rs, p.1 ≠ h ∧ p.2 < vals.length) →
    Runs s (readsEnv env vals rs) [k] s₂ res → res ≠ .err (.abort .timeoutError) →
    Runs s env [readsExp h rs k] s₂ res
  | [], env, s, s₂, k, res, _, _, _, hk, _ => hk
  | (n, j) :: rs, env, s, s₂, k, res, hh, hc, hrs, hk, hr => by
    have hj : j < vals.length := (hrs (n, j) (List.mem_cons_self ..)).2
    have hn : n ≠ h := (hrs (n, j) (List.mem_cons_self ..)).1
    have hv : Runs s env [handleAt h j] s (.val [vals[j]]) :=
      ⟨s.clock, s.clock, evaluate_asub_lit { s with clock := s.clock } hh hc hj⟩
    have hrest := Runs_reads rs { env with v := nsOptBind (some n) (vals.getD j (.conv none [])) env.v } s s₂ k
      res (nsl_ne hn hh) hc (fun p hp => hrs p (List.mem_cons_of_mem _ hp)) (by simpa [readsEnv] using hk) hr
    have hg : vals.getD j (.conv none []) = vals[j] := by simp [List.getD, hj]
    rw [hg] at hrest
    have := Runs.let_ (n := some n) hv hrest hr
    simpa [readsExp] using this

/-! ## Allocating fresh tables into variables -/

/-- `let f₁ = newTbl e₁ in … in k`. -/
def freshExp (a : VarN) : List (VarN × Exp) → Exp → Exp
  | [], k => k
  | (f, e) :: fs, k => .let_ (some f) (newTbl a e) (freshExp a fs k)

/-- The environment after `freshExp`, the new handles `hs`. -/
def freshEnv (env : SemEnv Value) : List VarN → List Value → SemEnv Value
  | f :: fs, v :: vs => freshEnv { env with v := nsOptBind (some f) v env.v } fs vs
  | _, _ => env

theorem freshEnv_c (env : SemEnv Value) : ∀ fs vs, (freshEnv env fs vs).c = env.c
  | f :: fs, v :: vs => by simp only [freshEnv]; rw [freshEnv_c _ fs vs]
  | [], _ => rfl
  | _ :: _, [] => rfl

/-- What allocating the fresh tables produces. -/
structure FreshOk (r r' : Store Value) (BIs : List (Σ K V : Type, RefInv (Bkt K V))) (hs : List Value) : Prop where
  pre : ∃ extra, r' = r ++ extra
  len : hs.length = BIs.length
  tbl : ∀ k (hk : k < BIs.length), ∃ tl, hs[k]'(by omega) = .loc true tl ∧
    ∀ raw : TRaw (BIs[k]).1 (BIs[k]).2.1, EmptyRaw raw → (tblRel (BIs[k]).2.2 tl).rel raw r'
  fresh : ∀ k (hk : k < BIs.length) l, tblOwns r' (hs[k]'(by omega)) l → r.length ≤ l
  disj : ∀ k₁ k₂ (h₁ : k₁ < BIs.length) (h₂ : k₂ < BIs.length), k₁ ≠ k₂ → ∀ l,
    tblOwns r' (hs[k₁]'(by omega)) l → ¬ tblOwns r' (hs[k₂]'(by omega)) l

theorem Runs_fresh {τ : Type} {a : VarN} :
    ∀ (fs : List (VarN × Exp)) (BIs : List (Σ K V : Type, RefInv (Bkt K V))) (env : SemEnv Value) (s : State τ)
    (_ : fs.length = BIs.length)
    (_ : ∀ k (hk : k < fs.length) ns, Eval { env with v := ns } (fs[k]).2 ((BIs[k]'(by omega)).2.2 .nil)),
    ∃ r' hs, FreshOk s.refs r' BIs hs ∧ ∀ (k : Exp) (s₂ : State τ) (res : Result (List Value) Value),
      Runs { s with refs := r' } (freshEnv env (fs.map (·.1)) hs) [k] s₂ res → res ≠ .err (.abort .timeoutError) →
      Runs s env [freshExp a fs k] s₂ res
  | [], BIs, env, s, hl, _ => by
    have : BIs = [] := by
      cases BIs with
      | nil => rfl
      | cons _ _ => exact absurd hl (by simp)
    subst this
    refine ⟨s.refs, [], ⟨⟨[], by simp⟩, rfl, fun k hk => by simp at hk, fun k hk => by simp at hk,
      fun k _ hk => by simp at hk⟩, fun k s₂ res hk _ => ?_⟩
    simpa [freshExp, freshEnv] using hk
  | (f, e) :: fs, BIs, env, s, hl, hnil => by
    obtain ⟨⟨K, V, BI⟩, BIs', rfl⟩ : ∃ x xs, BIs = x :: xs := by
      cases BIs with
      | nil => simp at hl
      | cons x xs => exact ⟨x, xs, rfl⟩
    have he : Eval env e (BI .nil) := hnil 0 (by simp) env.v
    obtain ⟨extra₁, vn, hrun₁, hB⟩ := Runs_newTbl (s := s) (a := a) he
    obtain ⟨A, hAd⟩ : ∃ A, A = s.refs.length + extra₁.length := ⟨_, rfl⟩
    obtain ⟨T, hTd⟩ : ∃ T, T = A + 1 := ⟨_, rfl⟩
    rw [← hAd, ← hTd] at hrun₁
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
    obtain ⟨r', hs', hok, hcont⟩ := Runs_fresh (a := a) fs BIs' { env with v := nsOptBind (some f) (.loc true T) env.v }
      { s with refs := r₁ } (by simpa using hl) (fun k hk ns => hnil (k + 1) (by simp; omega) ns)
    obtain ⟨extra₂, hr'⟩ := hok.pre
    have hkeep : ∀ l < r₁.length, r'[l]? = r₁[l]? := fun l hl => by
      rw [hr']; exact List.getElem?_append_left hl
    have hA' : r'[A]? = some (.varray (List.replicate 16 vn)) := by rw [hkeep A (by omega), hA₁]
    have hT' : r'[T]? = some (.varray [.loc true A, .litv (.intLit 0)]) := by rw [hkeep T (by omega), hT₁]
    have hnewOwn : ∀ l, tblOwns r' (.loc true T) l → l = T ∨ l = A := fun l ho => tblOwns_new hT' ho
    refine ⟨r', .loc true T :: hs', ⟨⟨extra₁ ++ [.varray (List.replicate 16 vn),
      .varray [.loc true A, .litv (.intLit 0)]] ++ extra₂, by rw [hr']; simp [r₁]⟩, by simp [hok.len],
      fun k hk => ?_, fun k hk l ho => ?_, fun k₁ k₂ h₁ h₂ hne l ho₁ ho₂ => ?_⟩, fun k s₂ res hk hr => ?_⟩
    · cases k with
      | zero => exact ⟨T, rfl, fun raw hraw => newTbl_rel hB hA' hT' (by omega) raw hraw⟩
      | succ k =>
        obtain ⟨tl, hv, htl⟩ := hok.tbl k (by simp at hk; omega)
        exact ⟨tl, by simpa using hv, by simpa using htl⟩
    · cases k with
      | zero => rcases hnewOwn l (by simpa using ho) with rfl | rfl <;> omega
      | succ k =>
        have := hok.fresh k (by simp at hk; omega) l (by simpa using ho)
        simp [r₁] at this; omega
    · cases k₁ with
      | zero =>
        cases k₂ with
        | zero => exact hne rfl
        | succ k₂ =>
          have := hok.fresh k₂ (by simp at h₂; omega) l (by simpa using ho₂)
          simp [r₁] at this
          rcases hnewOwn l (by simpa using ho₁) with rfl | rfl <;> omega
      | succ k₁ =>
        cases k₂ with
        | zero =>
          have := hok.fresh k₁ (by simp at h₁; omega) l (by simpa using ho₁)
          simp [r₁] at this
          rcases hnewOwn l (by simpa using ho₂) with rfl | rfl <;> omega
        | succ k₂ =>
          exact hok.disj k₁ k₂ (by simp at h₁; omega) (by simp at h₂; omega) (by omega) l
            (by simpa using ho₁) (by simpa using ho₂)
    · have hrest := hcont k s₂ res (by simpa [freshEnv] using hk) hr
      have := Runs.let_ (n := some f) hrun₁ hrest hr
      simpa [freshExp, r₁] using this

/-! ## Writing handles -/

/-- Where a written handle comes from: another field, or a variable. -/
inductive Src where
  | rd (j : Nat)
  | var (s : VarN)

def srcExp (h : VarN) : Src → Exp
  | .rd j => handleAt h j
  | .var s => .var (.short s)

/-- `let _ = Array.update h t₁ src₁ in … in k`. -/
def writesExp (h : VarN) : List (Nat × Src) → Exp → Exp
  | [], k => k
  | (t, src) :: ws, k => .let_ none (.app .aupdate [.var (.short h), .lit (.intLit ((t : Nat) : Int)), srcExp h src])
      (writesExp h ws k)

def srcVal (env : SemEnv Value) (vals : List Value) : Src → Value
  | .rd j => vals.getD j (.conv none [])
  | .var s => (nsLookup env.v (.short s)).getD (.conv none [])

/-- The handles after the writes. -/
def writesVals (env : SemEnv Value) : List Value → List (Nat × Src) → List Value
  | vals, [] => vals
  | vals, (t, src) :: ws => writesVals env (vals.set t (srcVal env vals src)) ws

theorem writesVals_length (env : SemEnv Value) : ∀ (vals : List Value) ws, (writesVals env vals ws).length = vals.length
  | _, [] => rfl
  | vals, (t, src) :: ws => by simp only [writesVals]; rw [writesVals_length]; simp

/-- A write's source evaluates, without changing the store. -/
theorem Runs_src {τ : Type} {s : State τ} {env : SemEnv Value} {h : VarN} {loc : Nat} {b₀ : Bool}
    {vals : List Value} (hh : nsLookup env.v (.short h) = some (.loc b₀ loc))
    (hc : s.refs[loc]? = some (.varray vals)) {src : Src}
    (hsrc : match src with | .rd j => j < vals.length | .var x => (nsLookup env.v (.short x)).isSome) :
    ∀ ck, evaluate { s with clock := ck } env [srcExp h src] = ({ s with clock := ck }, .val [srcVal env vals src]) := by
  intro ck
  cases src with
  | rd j =>
    have hj : j < vals.length := hsrc
    have := evaluate_asub_lit { s with clock := ck } hh hc hj
    simpa [srcExp, srcVal, List.getD, hj] using this
  | var x =>
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsrc
    simp [srcExp, srcVal, evaluate, hw]

theorem Runs_writes {τ : Type} {h : VarN} {loc : Nat} {b₀ : Bool} {env : SemEnv Value}
    (hh : nsLookup env.v (.short h) = some (.loc b₀ loc)) :
    ∀ (ws : List (Nat × Src)) (vals : List Value) (s s₂ : State τ) (k : Exp) (res : Result (List Value) Value),
    s.refs[loc]? = some (.varray vals) →
    (∀ p ∈ ws, p.1 < vals.length ∧ match p.2 with
      | .rd j => j < vals.length | .var x => (nsLookup env.v (.short x)).isSome) →
    Runs { s with refs := s.refs.set loc (.varray (writesVals env vals ws)) } env [k] s₂ res →
    res ≠ .err (.abort .timeoutError) →
    Runs s env [writesExp h ws k] s₂ res
  | [], vals, s, s₂, k, res, hc, _, hk, _ => by
    have hloc : loc < s.refs.length := (List.getElem?_eq_some_iff.mp hc).1
    have : s.refs.set loc (.varray vals) = s.refs := by
      apply List.ext_getElem?; intro l
      by_cases hl : l = loc
      · subst hl; rw [List.getElem?_set_self hloc, hc]
      · rw [List.getElem?_set_ne (Ne.symm hl)]
    simpa [writesExp, writesVals, this] using hk
  | (t, src) :: ws, vals, s, s₂, k, res, hc, hws, hk, hr => by
    have ht : t < vals.length := (hws (t, src) (List.mem_cons_self ..)).1
    have hsrc := (hws (t, src) (List.mem_cons_self ..)).2
    have hloc : loc < s.refs.length := (List.getElem?_eq_some_iff.mp hc).1
    let v := srcVal env vals src
    let r₁ := s.refs.set loc (.varray (vals.set t v))
    have hupd : Runs s env [.app .aupdate [.var (.short h), .lit (.intLit ((t : Nat) : Int)), srcExp h src]]
        { s with refs := r₁ } (.val [.conv none []]) := by
      refine ⟨s.clock, s.clock, ?_⟩
      have hargs : evaluate { s with clock := s.clock } env [srcExp h src, .lit (.intLit ((t : Nat) : Int)), .var (.short h)] =
          ({ s with clock := s.clock }, .val [v, .litv (.intLit t), .loc b₀ loc]) :=
        evaluate_cons_val (Runs_src hh hc hsrc s.clock)
          (evaluate_cons_val (s₁ := { s with clock := s.clock }) (by simp [evaluate]) (by simp [evaluate, hh]))
      have := evaluate_app_simple (s := { s with clock := s.clock }) (s₁ := { s with clock := s.clock })
        (env := env) (op := .aupdate) (args := [.var (.short h), .lit (.intLit ((t : Nat) : Int)), srcExp h src])
        (vs := [v, .litv (.intLit t), .loc b₀ loc]) (refs := r₁) (ffi := s.ffi) (r := .val (.conv none []))
        (by simpa using hargs) rfl
        (by
          have hneg : ¬ ((t : Int) < 0) := by omega
          have hle : ¬ (vals.length ≤ t) := by omega
          simp [doApp, doAppBasic, doAppNumericCore, storeLookup, hc, updateIndexed, hneg, hle,
            storeAssign, storeValueSameType, r₁])
      simpa [listResult] using this
    have hc₁ : r₁[loc]? = some (.varray (vals.set t v)) := List.getElem?_set_self hloc
    have hrest := Runs_writes hh ws (vals.set t v) { s with refs := r₁ } s₂ k res hc₁
      (fun p hp => by
        obtain ⟨h1, h2⟩ := hws p (List.mem_cons_of_mem _ hp)
        refine ⟨by simpa using h1, ?_⟩
        cases hq : p.2 with
        | rd j => rw [hq] at h2; simpa using h2
        | var x => rw [hq] at h2; exact h2)
      (by simpa [r₁, writesVals, List.set_set] using hk) hr
    have := Runs.let_ (n := none) hupd (by simpa [nsOptBind] using hrest) hr
    simpa [writesExp] using this

/-- The write to field `t`, if any. -/
def wlookup : List (Nat × Src) → Nat → Option Src
  | [], _ => none
  | (t₀, src) :: ws, t => if t = t₀ then some src else wlookup ws t

theorem wlookup_mem : ∀ (ws : List (Nat × Src)) (t : Nat) (src : Src), wlookup ws t = some src →
    ∃ p ∈ ws, p.1 = t ∧ p.2 = src
  | [], _, _, h => by simp [wlookup] at h
  | (t₀, s₀) :: ws, t, src, h => by
    simp only [wlookup] at h
    split at h
    · cases h; rename_i he; exact ⟨(t₀, s₀), List.mem_cons_self .., he.symm, rfl⟩
    · obtain ⟨p, hp, h1, h2⟩ := wlookup_mem ws t src h
      exact ⟨p, List.mem_cons_of_mem _ hp, h1, h2⟩

theorem wlookup_none : ∀ (ws : List (Nat × Src)) (t : Nat), t ∉ ws.map (·.1) → wlookup ws t = none
  | [], _, _ => rfl
  | (t₀, s₀) :: ws, t, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [wlookup, h.1, wlookup_none ws t h.2]

/-- The handle at `t` after writes to distinct fields reading only unwritten ones. -/
theorem writesVals_get (env : SemEnv Value) :
    ∀ (ws : List (Nat × Src)) (vals : List Value) (t : Nat),
    (ws.map (·.1)).Nodup → (∀ p ∈ ws, ∀ j, p.2 = .rd j → j ∉ ws.map (·.1)) → (∀ p ∈ ws, p.1 < vals.length) →
    (writesVals env vals ws)[t]? = match wlookup ws t with
      | some src => some (srcVal env vals src)
      | none => vals[t]?
  | [], vals, t, _, _, _ => by simp [writesVals, wlookup]
  | (t₀, src) :: ws, vals, t, hnd, hrd, hlt => by
    simp only [writesVals]
    have hnd' : (ws.map (·.1)).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
    have ht₀ : t₀ ∉ ws.map (·.1) := (List.nodup_cons.mp (by simpa using hnd)).1
    have hlt₀ : t₀ < vals.length := hlt _ (List.mem_cons_self ..)
    rw [writesVals_get env ws (vals.set t₀ (srcVal env vals src)) t hnd'
      (fun p hp j hj hm => hrd p (List.mem_cons_of_mem _ hp) j hj (List.mem_cons_of_mem _ hm))
      (fun p hp => by simpa using hlt p (List.mem_cons_of_mem _ hp))]
    have hsame : ∀ p ∈ ws, srcVal env (vals.set t₀ (srcVal env vals src)) p.2 = srcVal env vals p.2 := by
      intro p hp
      cases hq : p.2 with
      | var x => rfl
      | rd j =>
        have hj : j ≠ t₀ := fun he => hrd p (List.mem_cons_of_mem _ hp) j hq (by simp [he])
        simp [srcVal, List.getD, List.getElem?_set_ne (Ne.symm hj)]
    by_cases htt : t = t₀
    · subst htt
      simp [wlookup, wlookup_none ws t ht₀, List.getElem?_set_self hlt₀]
    · simp only [wlookup, htt, if_false]
      cases hl : wlookup ws t with
      | none => simp [List.getElem?_set_ne (Ne.symm htt)]
      | some src' =>
        obtain ⟨p, hp, _, hps⟩ := wlookup_mem ws t src' hl
        simp only
        rw [← hps, hsame p hp]

/-! ## Environments binding lists of names -/

/-- `ns` bound to `vs`, in order. -/
def bindAll (env : SemEnv Value) : List VarN → List Value → SemEnv Value
  | n :: ns, v :: vs => bindAll { env with v := nsOptBind (some n) v env.v } ns vs
  | _, _ => env

theorem bindAll_c (env : SemEnv Value) : ∀ ns vs, (bindAll env ns vs).c = env.c
  | n :: ns, v :: vs => by simp only [bindAll]; rw [bindAll_c _ ns vs]
  | [], _ => rfl
  | _ :: _, [] => rfl

theorem bindAll_ne (env : SemEnv Value) (y : VarN) : ∀ ns vs, y ∉ ns →
    nsLookup (bindAll env ns vs).v (.short y) = nsLookup env.v (.short y)
  | n :: ns, v :: vs, hy => by
    simp only [List.mem_cons, not_or] at hy
    simp only [bindAll]
    rw [bindAll_ne _ y ns vs hy.2]
    simp [nsOptBind, nsLookup_nsBind_short, hy.1]
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl

theorem bindAll_get (env : SemEnv Value) : ∀ (ns : List VarN) (vs : List Value) (_ : ns.Nodup)
    (_ : ns.length = vs.length) k (hk : k < ns.length),
    nsLookup (bindAll env ns vs).v (.short ns[k]) = some (vs[k]'(by omega))
  | n :: ns, v :: vs, hnd, hl, k, hk => by
    have hnd' := List.nodup_cons.mp hnd
    simp only [bindAll]
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero]
      rw [bindAll_ne _ n ns vs hnd'.1]
      simp [nsOptBind, nsLookup_nsBind_short]
    | succ k =>
      simp only [List.getElem_cons_succ]
      exact bindAll_get _ ns vs hnd'.2 (by simpa using hl) k (by simpa using hk)
  | [], _, _, _, k, hk => absurd hk (by simp)

theorem readsEnv_eq (env : SemEnv Value) (vals : List Value) : ∀ rs : List (VarN × Nat),
    readsEnv env vals rs = bindAll env (rs.map (·.1)) (rs.map fun p => vals.getD p.2 (.conv none []))
  | [] => rfl
  | (s, j) :: rs => by simp only [readsEnv, List.map_cons, bindAll]; rw [readsEnv_eq _ _ rs]

theorem freshEnv_eq (env : SemEnv Value) : ∀ fs vs, freshEnv env fs vs = bindAll env fs vs
  | f :: fs, v :: vs => by simp only [freshEnv, bindAll]; rw [freshEnv_eq _ fs vs]
  | [], _ => rfl
  | _ :: _, [] => rfl

/-! ## The state before and after the swap -/

section
variable {σ : Type} {tabs : σ → List TEntry} {P : σ → Value → Prop} {loc : Nat}

/-- Ownership by a handle whose table cell is unchanged. -/
theorem tblOwns_same {r r' : Store Value} {v : Value} {l : Nat}
    (hcell : ∀ b tl, v = .loc b tl → r'[tl]? = r[tl]?) : tblOwns r' v l ↔ tblOwns r v l := by
  constructor
  · rintro ⟨b, tl, rfl, h⟩
    exact (tblOwns_congr (hcell b tl rfl)).mp ⟨b, tl, rfl, h⟩
  · rintro ⟨b, tl, rfl, h⟩
    exact (tblOwns_congr (hcell b tl rfl)).mpr ⟨b, tl, rfl, h⟩

/-- An old table: its relation and ownership survive a store that agrees on old
cells other than the state's. -/
theorem old_tbl {st : σ} {r r' : Store Value} {vals : List Value} (hk : RecOk tabs P loc st r vals)
    (hsame : ∀ l < r.length, l ≠ loc → r'[l]? = r[l]?) (hlen : r.length ≤ r'.length)
    {j : Nat} (hj : j < (tabs st).length) :
    ∃ b tl, vals[j]'(by have := hk.len; omega) = .loc b tl ∧
      (tblRel ((tabs st)[j]).BI tl).rel ((tabs st)[j]).raw r' ∧
      ∀ l, tblOwns r' (vals[j]'(by have := hk.len; omega)) l ↔ tblOwns r (vals[j]'(by have := hk.len; omega)) l := by
  obtain ⟨b, tl, hv, ht⟩ := hk.tbl j hj
  have hown : ∀ l, (tblRel ((tabs st)[j]).BI tl).owns r l → r'[l]? = r[l]? := by
    intro l ho
    refine hsame l ((tblRel _ tl).inRange _ r ht l ho) ?_
    rintro rfl
    exact hk.noLoc j hj (by rw [hv]; exact tblOwns_loc.mpr ho)
  refine ⟨b, tl, hv, (tblRel _ tl).stable _ r r' ht hlen hown, fun l => ?_⟩
  rw [hv]
  exact tblOwns_congr (hown tl (Or.inl rfl))

end

section
variable {σ : Type} {tabs : σ → List TEntry} {P : σ → Value → Prop} {loc : Nat}

theorem getElem_of_getElem? {α : Type u} {l : List α} {i : Nat} {x : α} (hi : i < l.length) (h : l[i]? = some x) :
    l[i] = x := by
  rw [List.getElem?_eq_getElem hi] at h; exact Option.some.inj h

/-- **Entering the swap**: `vals₂` holds the old tables of the fields `ps·.2`
in the fields `ps·.1`, fresh tables in the fields `ps·.2`, the rest unchanged. -/
theorem swap_enter {st st₁ : σ} {r r₂ : Store Value} {vals vals₂ : List Value} {N : Nat}
    {ps : List (Nat × Nat)} {BIs : List (Σ K V : Type, RefInv (Bkt K V))} {fvs : List Value}
    (hk : RecOk tabs P loc st r vals) (hN : (tabs st).length = N) (hN₁ : (tabs st₁).length = N)
    (hps : ∀ p ∈ ps, p.1 < N ∧ p.2 < N) (hnd : (ps.map (·.1) ++ ps.map (·.2)).Nodup)
    (hfr : FreshOk r r₂ BIs fvs) (hBIs : BIs.length = ps.length)
    (hl₂ : vals₂.length = vals.length)
    (d1 : ∀ k (hk : k < ps.length), vals₂[(ps[k]).1]? = vals[(ps[k]).2]?)
    (d2 : ∀ k (hk : k < ps.length), vals₂[(ps[k]).2]? = fvs[k]?)
    (d3 : ∀ j, j ∉ ps.map (·.1) → j ∉ ps.map (·.2) → vals₂[j]? = vals[j]?)
    (E1 : ∀ j, j ∉ ps.map (·.1) → j ∉ ps.map (·.2) → (tabs st₁)[j]? = (tabs st)[j]?)
    (E2 : ∀ k (hk : k < ps.length) e e', (tabs st)[(ps[k]).2]? = some e → (tabs st₁)[(ps[k]).1]? = some e' →
      ∀ r tl, (tblRel e.BI tl).rel e.raw r → (tblRel e'.BI tl).rel e'.raw r)
    (E3 : ∀ k (hk : k < ps.length) e, (tabs st₁)[(ps[k]).2]? = some e → ∀ r tl,
      (∀ raw : TRaw (BIs[k]'(by omega)).1 (BIs[k]'(by omega)).2.1, EmptyRaw raw →
        (tblRel (BIs[k]'(by omega)).2.2 tl).rel raw r) → (tblRel e.BI tl).rel e.raw r)
    (P1 : ∀ v, P st₁ v ↔ P st v) :
    RecOk tabs P loc st₁ (r₂.set loc (.varray vals₂)) vals₂ ∧
      Frame (recRel tabs P loc) r (r₂.set loc (.varray vals₂)) ∧
      (∀ k (hk : k < ps.length) l, tblOwns r (vals.getD (ps[k]).1 (.conv none [])) l →
        ¬ (recRel tabs P loc).owns (r₂.set loc (.varray vals₂)) l) ∧
      (∀ l < r.length, l ≠ loc → (r₂.set loc (.varray vals₂))[l]? = r[l]?) := by
  obtain ⟨extra, hr₂⟩ := hfr.pre
  have hvl : vals.length = N + 1 := by rw [hk.len, hN]
  have hlocr : loc < r.length := (List.getElem?_eq_some_iff.mp hk.cell).1
  let r₃ := r₂.set loc (.varray vals₂)
  have hr₃len : r₃.length = r₂.length := by simp [r₃]
  have hr₂len : r.length ≤ r₂.length := by rw [hr₂]; simp
  have hsame : ∀ l < r.length, l ≠ loc → r₃[l]? = r[l]? := by
    intro l hl hne
    simp only [r₃]; rw [List.getElem?_set_ne (Ne.symm hne), hr₂, List.getElem?_append_left hl]
  have hsame₂ : ∀ l, l ≠ loc → r₃[l]? = r₂[l]? := fun l hne => by
    simp only [r₃]; rw [List.getElem?_set_ne (Ne.symm hne)]
  have hp1 : ∀ k (h : k < ps.length), (ps[k]).1 < N := fun k h => (hps _ (List.getElem_mem h)).1
  have hp2 : ∀ k (h : k < ps.length), (ps[k]).2 < N := fun k h => (hps _ (List.getElem_mem h)).2
  have hnd1 : (ps.map (·.1)).Nodup := (List.nodup_append.mp hnd).1
  have hnd2 : (ps.map (·.2)).Nodup := (List.nodup_append.mp hnd).2.1
  have hdisj12 : ∀ k₁ k₂ (h₁ : k₁ < ps.length) (h₂ : k₂ < ps.length), (ps[k₁]).1 ≠ (ps[k₂]).2 := by
    intro k₁ k₂ h₁ h₂ he
    have := (List.nodup_append.mp hnd).2.2
    exact this _ (List.mem_map.mpr ⟨_, List.getElem_mem h₁, rfl⟩) _ (List.mem_map.mpr ⟨_, List.getElem_mem h₂, rfl⟩) he
  have hinj1 : ∀ k₁ k₂ (h₁ : k₁ < ps.length) (h₂ : k₂ < ps.length), (ps[k₁]).1 = (ps[k₂]).1 → k₁ = k₂ := by
    intro k₁ k₂ h₁ h₂ he
    have h₁' : k₁ < (ps.map (·.1)).length := by simpa using h₁
    have h₂' : k₂ < (ps.map (·.1)).length := by simpa using h₂
    exact (List.Nodup.getElem_inj (hi := h₁') (hj := h₂') hnd1).mp (by simpa using he)
  have hinj2 : ∀ k₁ k₂ (h₁ : k₁ < ps.length) (h₂ : k₂ < ps.length), (ps[k₁]).2 = (ps[k₂]).2 → k₁ = k₂ := by
    intro k₁ k₂ h₁ h₂ he
    have h₁' : k₁ < (ps.map (·.2)).length := by simpa using h₁
    have h₂' : k₂ < (ps.map (·.2)).length := by simpa using h₂
    exact (List.Nodup.getElem_inj (hi := h₁') (hj := h₂') hnd2).mp (by simpa using he)
  have hfl : fvs.length = ps.length := by rw [hfr.len, hBIs]
  -- an old table at `vals[i]` (`i` not a field that moves out)
  have oldOk : ∀ i (hi : i < N), ∃ b tl, vals[i]? = some (.loc b tl) ∧
      (∃ e, (tabs st)[i]? = some e ∧ (tblRel e.BI tl).rel e.raw r₃) ∧
      ∀ l, tblOwns r₃ (.loc b tl) l ↔ tblOwns r (.loc b tl) l := by
    intro i hi
    obtain ⟨b, tl, hv, ht, hown⟩ := old_tbl hk hsame (by omega) (j := i) (by omega)
    refine ⟨b, tl, by rw [List.getElem?_eq_getElem (by omega), hv], ⟨_, List.getElem?_eq_getElem (by omega), ht⟩, ?_⟩
    intro l; have := hown l; rwa [hv] at this
  -- a fresh table
  have freshOk : ∀ k (hk : k < ps.length), ∃ tl, fvs[k]? = some (.loc true tl) ∧
      (∀ raw : TRaw (BIs[k]'(by omega)).1 (BIs[k]'(by omega)).2.1, EmptyRaw raw →
        (tblRel (BIs[k]'(by omega)).2.2 tl).rel raw r₃) ∧
      (∀ l, tblOwns r₃ (.loc true tl) l → r.length ≤ l) ∧
      ∀ l, tblOwns r₃ (.loc true tl) l ↔ tblOwns r₂ (fvs[k]'(by omega)) l := by
    intro k hk'
    obtain ⟨tl, hv, ht⟩ := hfr.tbl k (by omega)
    have hcells : ∀ l, tblOwns r₂ (.loc true tl) l → l ≠ loc := by
      intro l ho he; subst he
      have := hfr.fresh k (by omega) l (by rw [hv]; exact ho); omega
    have htl : r₃[tl]? = r₂[tl]? := hsame₂ tl (hcells tl ⟨true, tl, rfl, Or.inl rfl⟩)
    refine ⟨tl, by rw [List.getElem?_eq_getElem (by omega), hv], fun raw hraw => ?_, fun l ho => ?_, fun l => ?_⟩
    · have h₂ := ht raw hraw
      refine (tblRel _ tl).stable _ r₂ r₃ h₂ (by omega) fun l ho => hsame₂ l ?_
      exact hcells l (tblOwns_loc.mpr ho)
    · have := hfr.fresh k (by omega) l (by rw [hv]; exact (tblOwns_congr htl).mp ho)
      exact this
    · rw [hv]; exact tblOwns_congr htl
  -- classify the fields of `vals₂`: an old table (with its witness), or a fresh one
  have classify : ∀ j (hj : j < N),
      (∃ i, i < N ∧ i ∉ ps.map (·.1) ∧ vals₂[j]? = vals[i]? ∧
        (∀ e e', (tabs st)[i]? = some e → (tabs st₁)[j]? = some e' → ∀ r tl,
          (tblRel e.BI tl).rel e.raw r → (tblRel e'.BI tl).rel e'.raw r) ∧
        ((∃ k, ∃ hk : k < ps.length, j = (ps[k]).1 ∧ i = (ps[k]).2) ∨
          (j ∉ ps.map (·.1) ∧ j ∉ ps.map (·.2) ∧ i = j))) ∨
      (∃ k, ∃ hk : k < ps.length, j = (ps[k]).2 ∧ vals₂[j]? = fvs[k]?) := by
    intro j hj
    by_cases h1 : j ∈ ps.map (·.1)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h1
      obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hp
      refine Or.inl ⟨(ps[k]).2, hp2 k hk', fun hm => ?_, d1 k hk', E2 k hk', Or.inl ⟨k, hk', rfl, rfl⟩⟩
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
      obtain ⟨k', hk'', rfl⟩ := List.getElem_of_mem hq
      exact hdisj12 k' k hk'' hk' hqe
    · by_cases h2 : j ∈ ps.map (·.2)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h2
        obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hp
        exact Or.inr ⟨k, hk', rfl, d2 k hk'⟩
      · refine Or.inl ⟨j, hj, h1, d3 j h1 h2, fun e e' he he' r tl ht => ?_, Or.inr ⟨h1, h2, rfl⟩⟩
        rw [E1 j h1 h2, he] at he'
        cases he'; exact ht
  -- two old fields with the same source are the same field
  have srcInj : ∀ j₁ j₂ i,
      ((∃ k, ∃ hk : k < ps.length, j₁ = (ps[k]).1 ∧ i = (ps[k]).2) ∨ (j₁ ∉ ps.map (·.1) ∧ j₁ ∉ ps.map (·.2) ∧ i = j₁)) →
      ((∃ k, ∃ hk : k < ps.length, j₂ = (ps[k]).1 ∧ i = (ps[k]).2) ∨ (j₂ ∉ ps.map (·.1) ∧ j₂ ∉ ps.map (·.2) ∧ i = j₂)) →
      j₁ = j₂ := by
    rintro j₁ j₂ i (⟨k₁, h₁, rfl, rfl⟩ | ⟨n₁, m₁, rfl⟩) (⟨k₂, h₂, rfl, he⟩ | ⟨n₂, m₂, he⟩)
    · obtain rfl := hinj2 k₁ k₂ h₁ h₂ he; rfl
    · exact absurd (by rw [← he]; exact List.mem_map_of_mem (f := (·.2)) (List.getElem_mem h₁)) m₂
    · exact absurd (by rw [he]; exact List.mem_map_of_mem (f := (·.2)) (List.getElem_mem h₂)) m₁
    · exact he
  -- the facts of each field: its handle, relation and cells
  have field : ∀ j (hj : j < N), ∃ b tl, vals₂[j]? = some (.loc b tl) ∧
      (∃ e, (tabs st₁)[j]? = some e ∧ (tblRel e.BI tl).rel e.raw r₃) ∧
      ((∃ i, i < N ∧ i ∉ ps.map (·.1) ∧ vals[i]? = some (.loc b tl) ∧
          ((∃ k, ∃ hk : k < ps.length, j = (ps[k]).1 ∧ i = (ps[k]).2) ∨
            (j ∉ ps.map (·.1) ∧ j ∉ ps.map (·.2) ∧ i = j)) ∧
          ∀ l, tblOwns r₃ (.loc b tl) l ↔ tblOwns r (.loc b tl) l) ∨
        (∃ k, ∃ hk : k < ps.length, j = (ps[k]).2 ∧ fvs[k]? = some (.loc b tl) ∧
          ∀ l, tblOwns r₃ (.loc b tl) l → r.length ≤ l)) := by
    intro j hj
    rcases classify j hj with ⟨i, hi, hni, hv, htr, hw⟩ | ⟨k, hk', rfl, hv⟩
    · obtain ⟨b, tl, hvi, ⟨e, he, ht⟩, hown⟩ := oldOk i hi
      obtain ⟨e', he'⟩ : ∃ e', (tabs st₁)[j]? = some e' :=
        ⟨_, List.getElem?_eq_getElem (by rw [hN₁]; exact hj)⟩
      exact ⟨b, tl, by rw [hv, hvi], ⟨e', he', htr e e' he he' r₃ tl ht⟩, Or.inl ⟨i, hi, hni, hvi, hw, hown⟩⟩
    · obtain ⟨tl, hvk, ht, hfresh, _⟩ := freshOk k hk'
      obtain ⟨e', he'⟩ : ∃ e', (tabs st₁)[(ps[k]).2]? = some e' :=
        ⟨_, List.getElem?_eq_getElem (by rw [hN₁]; exact hj)⟩
      exact ⟨true, tl, by rw [hv, hvk], ⟨e', he', E3 k hk' e' he' r₃ tl ht⟩,
        Or.inr ⟨k, hk', rfl, hvk, hfresh⟩⟩
  have hl₂' : vals₂.length = N + 1 := by rw [hl₂, hvl]
  have hcell₃ : r₃[loc]? = some (.varray vals₂) := by
    simp only [r₃]; rw [List.getElem?_set_self (by omega)]
  -- the handle of a field, by `getElem`
  have hget : ∀ j (hj : j < N) b tl, vals₂[j]? = some (.loc b tl) → vals₂[j]'(by omega) = .loc b tl :=
    fun j hj b tl h => getElem_of_getElem? (by omega) h
  refine ⟨⟨hcell₃, by rw [hl₂', hN₁], ?_, fun j hj => ?_, fun j₁ j₂ h₁ h₂ hne l ho₁ ho₂ => ?_, fun j hj ho => ?_⟩,
    ⟨by simp only [r₃, List.length_set]; omega, fun l hl hn => hsame l hl (fun he => hn (Or.inl he)),
      fun l hl ho => ?_⟩,
    fun k hk' l ho hro => ?_, hsame⟩
  · -- the plain part
    have hNo1 : N ∉ ps.map (·.1) := fun hm => by
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hm; exact absurd (he ▸ (hps p hp).1) (Nat.lt_irrefl N)
    have hNo2 : N ∉ ps.map (·.2) := fun hm => by
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hm; exact absurd (he ▸ (hps p hp).2) (Nat.lt_irrefl N)
    have h3 := d3 N hNo1 hNo2
    have hpl := hk.plain
    have e1 : vals₂[(tabs st₁).length]'(by omega) = vals[(tabs st).length]'(by omega) := by
      apply Option.some.inj
      rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hN, hN₁, h3]
    rw [e1]; exact (P1 _).mpr hpl
  · -- each field
    have hj' : j < N := by omega
    obtain ⟨b, tl, hv, ⟨e, he, ht⟩, _⟩ := field j hj'
    refine ⟨b, tl, hget j hj' b tl hv, ?_⟩
    rw [getElem_of_getElem? (by omega) he]; exact ht
  · -- disjoint
    have h₁' : j₁ < N := by omega
    have h₂' : j₂ < N := by omega
    obtain ⟨b₁, tl₁, hv₁, _, hc₁⟩ := field j₁ h₁'
    obtain ⟨b₂, tl₂, hv₂, _, hc₂⟩ := field j₂ h₂'
    rw [hget j₁ h₁' b₁ tl₁ hv₁] at ho₁
    rw [hget j₂ h₂' b₂ tl₂ hv₂] at ho₂
    rcases hc₁ with ⟨i₁, hi₁, _, hvi₁, hw₁, hown₁⟩ | ⟨k₁, hk₁, rfl, hvk₁, hf₁⟩ <;>
      rcases hc₂ with ⟨i₂, hi₂, _, hvi₂, hw₂, hown₂⟩ | ⟨k₂, hk₂, rfl, hvk₂, hf₂⟩
    · -- two old tables, from different sources
      have hii : i₁ ≠ i₂ := fun he => hne (srcInj j₁ j₂ i₁ hw₁ (by rw [he]; exact hw₂))
      have := hk.disj i₁ i₂ (by omega) (by omega) hii l
      rw [getElem_of_getElem? (by omega) hvi₁, getElem_of_getElem? (by omega) hvi₂] at this
      exact this ((hown₁ l).mp ho₁) ((hown₂ l).mp ho₂)
    · have := hf₂ l ho₂
      have := hk.tblOwns_lt (j := i₁) (by omega) (by rw [getElem_of_getElem? (by omega) hvi₁]; exact (hown₁ l).mp ho₁)
      omega
    · have := hf₁ l ho₁
      have := hk.tblOwns_lt (j := i₂) (by omega) (by rw [getElem_of_getElem? (by omega) hvi₂]; exact (hown₂ l).mp ho₂)
      omega
    · -- two fresh tables
      have hkk : k₁ ≠ k₂ := fun he => by subst he; exact hne rfl
      obtain ⟨tl₁', hv₁', _, _, hiff₁⟩ := freshOk k₁ hk₁
      obtain ⟨tl₂', hv₂', _, _, hiff₂⟩ := freshOk k₂ hk₂
      rw [hvk₁] at hv₁'; cases hv₁'
      rw [hvk₂] at hv₂'; cases hv₂'
      exact hfr.disj k₁ k₂ (by omega) (by omega) hkk l ((hiff₁ l).mp ho₁) ((hiff₂ l).mp ho₂)
  · -- not the state's cell
    have hj' : j < N := by omega
    obtain ⟨b, tl, hv, _, hc⟩ := field j hj'
    rw [hget j hj' b tl hv] at ho
    rcases hc with ⟨i, hi, _, hvi, _, hown⟩ | ⟨k, hk', _, _, hf⟩
    · have := hk.noLoc i (by omega)
      rw [getElem_of_getElem? (by omega) hvi] at this
      exact this ((hown loc).mp ho)
    · have := hf loc ho; omega
  · -- owned cells were owned
    rcases ho with rfl | ⟨vals', hc, j, hj, ho⟩
    · exact Or.inl rfl
    · rw [hcell₃] at hc
      simp only [Option.some.injEq, StoreValue.varray.injEq] at hc
      subst hc
      have hj' : j < N := by omega
      obtain ⟨b, tl, hv, _, hcl⟩ := field j hj'
      rw [hget j hj' b tl hv] at ho
      rcases hcl with ⟨i, hi, _, hvi, _, hown⟩ | ⟨k, hk', _, _, hf⟩
      · exact Or.inr ⟨vals, hk.cell, i, by omega, by
          rw [getElem_of_getElem? (by omega) hvi]; exact (hown l).mp ho⟩
      · have := hf l ho; omega
  · -- the saved tables are not the state's any more
    have hp1k := hp1 k hk'
    have hvs := hk.tbl (ps[k]).1 (by omega)
    obtain ⟨bs, tls, hvs', _⟩ := hvs
    have hgd : vals.getD (ps[k]).1 (.conv none []) = .loc bs tls := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), hvs']; rfl
    rw [hgd] at ho
    have hlr : l < r.length := hk.tblOwns_lt (j := (ps[k]).1) (by omega) (by rw [hvs']; exact ho)
    rcases hro with rfl | ⟨vals', hc, j, hj, hoj⟩
    · have := hk.noLoc (ps[k]).1 (by omega); rw [hvs'] at this; exact this ho
    · rw [hcell₃] at hc
      simp only [Option.some.injEq, StoreValue.varray.injEq] at hc
      subst hc
      have hj' : j < N := by omega
      obtain ⟨b, tl, hv, _, hcl⟩ := field j hj'
      rw [hget j hj' b tl hv] at hoj
      rcases hcl with ⟨i, hi, hni, hvi, _, hown⟩ | ⟨k', hk'', _, _, hf⟩
      · have hne : i ≠ (ps[k]).1 := fun he => hni (by rw [he]; exact List.mem_map.mpr ⟨_, List.getElem_mem hk', rfl⟩)
        have := hk.disj i (ps[k]).1 (by omega) (by omega) hne l
        rw [getElem_of_getElem? (by omega) hvi, hvs'] at this
        exact this ((hown l).mp hoj) ho
      · have := hf l hoj; omega

/-- **Leaving the swap**: the saved tables return to the fields `ps·.1`, the
tables of the fields `ps·.1` move to the fields `ps·.2`, the rest stays. -/
theorem swap_leave {st st₂ st₃ : σ} {r r₃ r₄ : Store Value} {vals valsX valsZ : List Value} {N : Nat}
    {ps : List (Nat × Nat)}
    (hk : RecOk tabs P loc st r vals) (hkX : RecOk tabs P loc st₂ r₄ valsX)
    (hN : (tabs st).length = N) (hN₂ : (tabs st₂).length = N) (hN₃ : (tabs st₃).length = N)
    (hps : ∀ p ∈ ps, p.1 < N ∧ p.2 < N) (hnd : (ps.map (·.1) ++ ps.map (·.2)).Nodup)
    (hfr₁ : Frame (recRel tabs P loc) r r₃) (hfr₄ : Frame (recRel tabs P loc) r₃ r₄)
    (hsaved : ∀ k (hk : k < ps.length) l, tblOwns r (vals.getD (ps[k]).1 (.conv none [])) l →
      ¬ (recRel tabs P loc).owns r₃ l)
    (hsame₃ : ∀ l < r.length, l ≠ loc → r₃[l]? = r[l]?)
    (hlZ : valsZ.length = valsX.length)
    (z1 : ∀ k (hk : k < ps.length), valsZ[(ps[k]).1]? = vals[(ps[k]).1]?)
    (z2 : ∀ k (hk : k < ps.length), valsZ[(ps[k]).2]? = valsX[(ps[k]).1]?)
    (z3 : ∀ j, j ∉ ps.map (·.1) → j ∉ ps.map (·.2) → valsZ[j]? = valsX[j]?)
    (L1 : ∀ j, j ∉ ps.map (·.1) → j ∉ ps.map (·.2) → (tabs st₃)[j]? = (tabs st₂)[j]?)
    (L2 : ∀ k (hk : k < ps.length), (tabs st₃)[(ps[k]).1]? = (tabs st)[(ps[k]).1]?)
    (L3 : ∀ k (hk : k < ps.length) e e', (tabs st₂)[(ps[k]).1]? = some e → (tabs st₃)[(ps[k]).2]? = some e' →
      ∀ r tl, (tblRel e.BI tl).rel e.raw r → (tblRel e'.BI tl).rel e'.raw r)
    (P2 : ∀ v, P st₃ v ↔ P st₂ v) :
    RecOk tabs P loc st₃ (r₄.set loc (.varray valsZ)) valsZ ∧
      Frame (recRel tabs P loc) r (r₄.set loc (.varray valsZ)) := by
  have hvl : vals.length = N + 1 := by rw [hk.len, hN]
  have hvXl : valsX.length = N + 1 := by rw [hkX.len, hN₂]
  have hlocr : loc < r.length := (List.getElem?_eq_some_iff.mp hk.cell).1
  have hloc₄ : loc < r₄.length := (List.getElem?_eq_some_iff.mp hkX.cell).1
  let r₅ := r₄.set loc (.varray valsZ)
  have hr₃len : r.length ≤ r₃.length := hfr₁.1
  have hr₄len : r₃.length ≤ r₄.length := hfr₄.1
  have hsame₅ : ∀ l, l ≠ loc → r₅[l]? = r₄[l]? := fun l hne => by
    simp only [r₅]; rw [List.getElem?_set_ne (Ne.symm hne)]
  have hp1 : ∀ k (h : k < ps.length), (ps[k]).1 < N := fun k h => (hps _ (List.getElem_mem h)).1
  have hp2 : ∀ k (h : k < ps.length), (ps[k]).2 < N := fun k h => (hps _ (List.getElem_mem h)).2
  have hnd1 : (ps.map (·.1)).Nodup := (List.nodup_append.mp hnd).1
  have hnd2 : (ps.map (·.2)).Nodup := (List.nodup_append.mp hnd).2.1
  have hdisj12 : ∀ k₁ k₂ (h₁ : k₁ < ps.length) (h₂ : k₂ < ps.length), (ps[k₁]).1 ≠ (ps[k₂]).2 := by
    intro k₁ k₂ h₁ h₂ he
    have := (List.nodup_append.mp hnd).2.2
    exact this _ (List.mem_map.mpr ⟨_, List.getElem_mem h₁, rfl⟩) _ (List.mem_map.mpr ⟨_, List.getElem_mem h₂, rfl⟩) he
  have hinj1 : ∀ k₁ k₂ (h₁ : k₁ < ps.length) (h₂ : k₂ < ps.length), (ps[k₁]).1 = (ps[k₂]).1 → k₁ = k₂ := by
    intro k₁ k₂ h₁ h₂ he
    have h₁' : k₁ < (ps.map (·.1)).length := by simpa using h₁
    have h₂' : k₂ < (ps.map (·.1)).length := by simpa using h₂
    exact (List.Nodup.getElem_inj (hi := h₁') (hj := h₂') hnd1).mp (by simpa using he)
  -- a saved table: unchanged since the start
  have savedOk : ∀ k (hk' : k < ps.length), ∃ b tl, vals[(ps[k]).1]? = some (.loc b tl) ∧
      (∃ e, (tabs st)[(ps[k]).1]? = some e ∧ (tblRel e.BI tl).rel e.raw r₅) ∧
      ∀ l, tblOwns r₅ (.loc b tl) l ↔ tblOwns r (.loc b tl) l := by
    intro k hk'
    have hi : (ps[k]).1 < (tabs st).length := by rw [hN]; exact hp1 k hk'
    obtain ⟨b, tl, hv, ht⟩ := hk.tbl _ hi
    have hgd : vals.getD (ps[k]).1 (.conv none []) = .loc b tl := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), hv]; rfl
    -- its cells: old, not the state's, never owned by the state since the swap
    have hcells : ∀ l, tblOwns r (.loc b tl) l → r₅[l]? = r[l]? := by
      intro l ho
      have hlr : l < r.length := hk.tblOwns_lt (j := (ps[k]).1) hi (by rw [hv]; exact ho)
      have hne : l ≠ loc := by rintro rfl; exact hk.noLoc _ hi (by rw [hv]; exact ho)
      have hno : ¬ (recRel tabs P loc).owns r₃ l := hsaved k hk' l (by rw [hgd]; exact ho)
      rw [hsame₅ l hne, hfr₄.2.1 l (by omega) hno, hsame₃ l hlr hne]
    refine ⟨b, tl, by rw [List.getElem?_eq_getElem (by omega), hv], ⟨_, List.getElem?_eq_getElem hi, ?_⟩, ?_⟩
    · exact (tblRel _ tl).stable _ r r₅ ht (by simp [r₅]; omega)
        fun l ho => hcells l (tblOwns_loc.mpr ho)
    · intro l; exact tblOwns_congr (hcells tl ⟨b, tl, rfl, Or.inl rfl⟩)
  -- a table of the run: unchanged by the last writes
  have xOk : ∀ i (hi : i < N), ∃ b tl, valsX[i]? = some (.loc b tl) ∧
      (∃ e, (tabs st₂)[i]? = some e ∧ (tblRel e.BI tl).rel e.raw r₅) ∧
      ∀ l, tblOwns r₅ (.loc b tl) l ↔ tblOwns r₄ (.loc b tl) l := by
    intro i hi
    have hi' : i < (tabs st₂).length := by rw [hN₂]; exact hi
    obtain ⟨b, tl, hv, ht⟩ := hkX.tbl i hi'
    have hcells : ∀ l, tblOwns r₄ (.loc b tl) l → r₅[l]? = r₄[l]? := by
      intro l ho
      exact hsame₅ l (by rintro rfl; exact hkX.noLoc i hi' (by rw [hv]; exact ho))
    refine ⟨b, tl, by rw [List.getElem?_eq_getElem (by omega), hv], ⟨_, List.getElem?_eq_getElem hi', ?_⟩, ?_⟩
    · exact (tblRel _ tl).stable _ r₄ r₅ ht (by simp [r₅]) fun l ho => hcells l (tblOwns_loc.mpr ho)
    · intro l; exact tblOwns_congr (hcells tl ⟨b, tl, rfl, Or.inl rfl⟩)
  -- the fields of `valsZ`
  have field : ∀ j (hj : j < N), ∃ b tl, valsZ[j]? = some (.loc b tl) ∧
      (∃ e, (tabs st₃)[j]? = some e ∧ (tblRel e.BI tl).rel e.raw r₅) ∧
      ((∃ k, ∃ hk : k < ps.length, j = (ps[k]).1 ∧ vals[(ps[k]).1]? = some (.loc b tl) ∧
          ∀ l, tblOwns r₅ (.loc b tl) l ↔ tblOwns r (.loc b tl) l) ∨
        (∃ i, i < N ∧ valsX[i]? = some (.loc b tl) ∧
          ((∃ k, ∃ hk : k < ps.length, j = (ps[k]).2 ∧ i = (ps[k]).1) ∨
            (j ∉ ps.map (·.1) ∧ j ∉ ps.map (·.2) ∧ i = j)) ∧
          ∀ l, tblOwns r₅ (.loc b tl) l ↔ tblOwns r₄ (.loc b tl) l)) := by
    intro j hj
    by_cases h1 : j ∈ ps.map (·.1)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h1
      obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hp
      obtain ⟨b, tl, hv, ⟨e, he, ht⟩, hown⟩ := savedOk k hk'
      refine ⟨b, tl, by rw [z1 k hk', hv], ⟨e, by rw [L2 k hk', he], ht⟩, Or.inl ⟨k, hk', rfl, hv, hown⟩⟩
    · by_cases h2 : j ∈ ps.map (·.2)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h2
        obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hp
        obtain ⟨b, tl, hv, ⟨e, he, ht⟩, hown⟩ := xOk (ps[k]).1 (hp1 k hk')
        obtain ⟨e', he'⟩ : ∃ e', (tabs st₃)[(ps[k]).2]? = some e' :=
          ⟨_, List.getElem?_eq_getElem (by rw [hN₃]; exact hj)⟩
        exact ⟨b, tl, by rw [z2 k hk', hv], ⟨e', he', L3 k hk' e e' he he' r₅ tl ht⟩,
          Or.inr ⟨_, hp1 k hk', hv, Or.inl ⟨k, hk', rfl, rfl⟩, hown⟩⟩
      · obtain ⟨b, tl, hv, ⟨e, he, ht⟩, hown⟩ := xOk j hj
        exact ⟨b, tl, by rw [z3 j h1 h2, hv], ⟨e, by rw [L1 j h1 h2, he], ht⟩,
          Or.inr ⟨j, hj, hv, Or.inr ⟨h1, h2, rfl⟩, hown⟩⟩
  have hlZ' : valsZ.length = N + 1 := by rw [hlZ, hvXl]
  have hcell₅ : r₅[loc]? = some (.varray valsZ) := by
    simp only [r₅]; rw [List.getElem?_set_self hloc₄]
  have hget : ∀ j (hj : j < N) b tl, valsZ[j]? = some (.loc b tl) → valsZ[j]'(by omega) = .loc b tl :=
    fun j hj b tl h => getElem_of_getElem? (by omega) h
  -- a cell of a run table, below the start, was the state's at the start
  have xBack : ∀ i (hi : i < N) b tl l, valsX[i]? = some (.loc b tl) → tblOwns r₄ (.loc b tl) l →
      l < r.length → (recRel tabs P loc).owns r l := by
    intro i hi b tl l hv ho hl
    have ho₄ : (recRel tabs P loc).owns r₄ l :=
      Or.inr ⟨valsX, hkX.cell, i, by omega, by rw [getElem_of_getElem? (by omega) hv]; exact ho⟩
    exact hfr₁.2.2 l hl (hfr₄.2.2 l (by omega) ho₄)
  refine ⟨⟨hcell₅, by rw [hlZ', hN₃], ?_, fun j hj => ?_, fun j₁ j₂ h₁ h₂ hne l ho₁ ho₂ => ?_, fun j hj ho => ?_⟩,
    ⟨by simp only [r₅, List.length_set]; omega, fun l hl hn => ?_, fun l hl ho => ?_⟩⟩
  · -- the plain part
    have hNo1 : N ∉ ps.map (·.1) := fun hm => by
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hm; exact absurd (he ▸ (hps p hp).1) (Nat.lt_irrefl N)
    have hNo2 : N ∉ ps.map (·.2) := fun hm => by
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hm; exact absurd (he ▸ (hps p hp).2) (Nat.lt_irrefl N)
    have h3 := z3 N hNo1 hNo2
    have hpl := hkX.plain
    have e1 : valsZ[(tabs st₃).length]'(by omega) = valsX[(tabs st₂).length]'(by omega) := by
      apply Option.some.inj
      rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hN₂, hN₃, h3]
    rw [e1]; exact (P2 _).mpr hpl
  · have hj' : j < N := by omega
    obtain ⟨b, tl, hv, ⟨e, he, ht⟩, _⟩ := field j hj'
    refine ⟨b, tl, hget j hj' b tl hv, ?_⟩
    rw [getElem_of_getElem? (by omega) he]; exact ht
  · have h₁' : j₁ < N := by omega
    have h₂' : j₂ < N := by omega
    obtain ⟨b₁, tl₁, hv₁, _, hc₁⟩ := field j₁ h₁'
    obtain ⟨b₂, tl₂, hv₂, _, hc₂⟩ := field j₂ h₂'
    rw [hget j₁ h₁' b₁ tl₁ hv₁] at ho₁
    rw [hget j₂ h₂' b₂ tl₂ hv₂] at ho₂
    rcases hc₁ with ⟨k₁, hk₁, rfl, hs₁, hown₁⟩ | ⟨i₁, hi₁, hx₁, hw₁, hown₁⟩ <;>
      rcases hc₂ with ⟨k₂, hk₂, rfl, hs₂, hown₂⟩ | ⟨i₂, hi₂, hx₂, hw₂, hown₂⟩
    · -- two saved tables
      have hne' : (ps[k₁]).1 ≠ (ps[k₂]).1 := hne
      have := hk.disj _ _ (by rw [hN]; exact hp1 k₁ hk₁) (by rw [hN]; exact hp1 k₂ hk₂) hne' l
      rw [getElem_of_getElem? (by omega) hs₁, getElem_of_getElem? (by omega) hs₂] at this
      exact this ((hown₁ l).mp ho₁) ((hown₂ l).mp ho₂)
    · -- saved against a run table
      have hor := (hown₁ l).mp ho₁
      have hl : l < r.length := hk.tblOwns_lt (j := (ps[k₁]).1) (by rw [hN]; exact hp1 k₁ hk₁)
        (by rw [getElem_of_getElem? (by omega) hs₁]; exact hor)
      have hgd : vals.getD (ps[k₁]).1 (.conv none []) = .loc b₁ tl₁ := by
        rw [List.getD_eq_getElem?_getD, hs₁]; rfl
      have ho₄ : (recRel tabs P loc).owns r₄ l :=
        Or.inr ⟨valsX, hkX.cell, i₂, by omega, by rw [getElem_of_getElem? (by omega) hx₂]; exact (hown₂ l).mp ho₂⟩
      exact hsaved k₁ hk₁ l (by rw [hgd]; exact hor) (hfr₄.2.2 l (by omega) ho₄)
    · have hor := (hown₂ l).mp ho₂
      have hl : l < r.length := hk.tblOwns_lt (j := (ps[k₂]).1) (by rw [hN]; exact hp1 k₂ hk₂)
        (by rw [getElem_of_getElem? (by omega) hs₂]; exact hor)
      have hgd : vals.getD (ps[k₂]).1 (.conv none []) = .loc b₂ tl₂ := by
        rw [List.getD_eq_getElem?_getD, hs₂]; rfl
      have ho₄ : (recRel tabs P loc).owns r₄ l :=
        Or.inr ⟨valsX, hkX.cell, i₁, by omega, by rw [getElem_of_getElem? (by omega) hx₁]; exact (hown₁ l).mp ho₁⟩
      exact hsaved k₂ hk₂ l (by rw [hgd]; exact hor) (hfr₄.2.2 l (by omega) ho₄)
    · -- two run tables, from different fields
      have hii : i₁ ≠ i₂ := by
        rintro rfl
        rcases hw₁ with ⟨k₁, hk₁, rfl, rfl⟩ | ⟨n₁, m₁, rfl⟩ <;>
          rcases hw₂ with ⟨k₂, hk₂, rfl, he⟩ | ⟨n₂, m₂, he⟩
        · obtain rfl := hinj1 k₁ k₂ hk₁ hk₂ he; exact hne rfl
        · exact n₂ (by rw [← he]; exact List.mem_map_of_mem (f := (·.1)) (List.getElem_mem hk₁))
        · exact n₁ (by rw [he]; exact List.mem_map_of_mem (f := (·.1)) (List.getElem_mem hk₂))
        · exact hne he
      have := hkX.disj i₁ i₂ (by omega) (by omega) hii l
      rw [getElem_of_getElem? (by omega) hx₁, getElem_of_getElem? (by omega) hx₂] at this
      exact this ((hown₁ l).mp ho₁) ((hown₂ l).mp ho₂)
  · have hj' : j < N := by omega
    obtain ⟨b, tl, hv, _, hc⟩ := field j hj'
    rw [hget j hj' b tl hv] at ho
    rcases hc with ⟨k, hk', _, hs, hown⟩ | ⟨i, hi, hx, _, hown⟩
    · have := hk.noLoc (ps[k]).1 (by rw [hN]; exact hp1 k hk')
      rw [getElem_of_getElem? (by omega) hs] at this
      exact this ((hown loc).mp ho)
    · have := hkX.noLoc i (by omega)
      rw [getElem_of_getElem? (by omega) hx] at this
      exact this ((hown loc).mp ho)
  · -- unowned cells unchanged
    have hne : l ≠ loc := fun he => hn (Or.inl he)
    have hn₃ : ¬ (recRel tabs P loc).owns r₃ l := fun ho => hn (hfr₁.2.2 l hl ho)
    rw [hsame₅ l hne, hfr₄.2.1 l (by omega) hn₃, hfr₁.2.1 l hl hn]
  · -- owned cells were owned
    rcases ho with rfl | ⟨vals', hc, j, hj, hoj⟩
    · exact Or.inl rfl
    · rw [hcell₅] at hc
      simp only [Option.some.injEq, StoreValue.varray.injEq] at hc
      subst hc
      have hj' : j < N := by omega
      obtain ⟨b, tl, hv, _, hcl⟩ := field j hj'
      rw [hget j hj' b tl hv] at hoj
      rcases hcl with ⟨k, hk', _, hs, hown⟩ | ⟨i, hi, hx, _, hown⟩
      · exact Or.inr ⟨vals, hk.cell, (ps[k]).1, by omega, by
          rw [getElem_of_getElem? (by omega) hs]; exact (hown l).mp hoj⟩
      · exact xBack i hi b tl l hx ((hown l).mp hoj) hl

end

end ConPastel.Translator
