import ConLeche.Verify.Cached.StreamIndex

/-!
# The fold from its jobs, both directions

con-leche splits its declaration fold `checkDecls` into independent jobs: build the index of the
whole stream once (`buildIndex`), then check each record at the index's view of its position
(`recordJob`). con-leche proves the accept direction: every job passing is an accept of the fold
(`checkDecls_of_jobs`).

The parallel mode of con-pastel decides by the job with the smallest index that does not pass, so it
also needs the reject direction, proved here: if every job before position `k` passes and job `k`
fails with error `e`, the fold fails with `e` at position `k` (`checkDecls_error_of_jobs`).

`jobsVerdict` is the in-order walk over the jobs, and `jobsVerdict_eq` says it is the fold's verdict:
`checkDecls` accepts exactly when every job passes.
-/

namespace ConPastel.Par

open ConLeche ConLeche.Cached

variable {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat}

/-- The fold's index after an accepting prefix is a twin of the view of the next position. -/
theorem twin_at {ds : Array Declaration} {k : Nat} {fe : FEnv} (hk' : k < ds.size)
    (hchain : PushChain Env.empty fe) (hfe : fe = mkFEnv (streamEnv (ds.toList.take k))) :
    Twin fe ((buildIndex ds).view k) := by
  have hkl : (ds.toList.take k).length = k := by simp; omega
  have hsplit : ds.toList.take k ++ ds.toList.drop k = ds.toList := List.take_append_drop k _
  have hI : IndexSpec (ds.toList.take k ++ ds.toList.drop k) (buildIndex ds) := by
    rw [hsplit]; exact buildIndex_spec ds
  have hnd : ((recsConsts (ds.toList.take k)).map (·.name)).Nodup := by
    have hN : NodupNames fe.env := hchain.2.2.1 (by simp [NodupNames, Env.empty])
    have hc : fe.env.consts = (recsConsts (ds.toList.take k)).reverse := by
      rw [hfe]
      show (streamEnv (ds.toList.take k)).consts = _
      simpa [Env.empty] using streamEnv_consts (ds.toList.take k) Env.empty
    unfold NodupNames at hN
    rw [hc, List.map_reverse] at hN
    exact (List.reverse_perm _).nodup_iff.mp hN
  exact hkl ▸ viewTwin hI hfe hnd

/-- `jobs_run` with the hypothesis on a prefix of the jobs only: if the jobs before `m` pass, the
fold runs through the first `m` records, to the environment they denote. -/
theorem jobs_run_upto {ds : Array Declaration} {m : Nat}
    (h : ∀ j (hj : j < ds.size), j < m →
      recordJob mode pins maxNatSize (buildIndex ds) j ds[j] = .ok ()) :
    ∀ k, k ≤ ds.size → k ≤ m → ∃ fe,
      DeclsRun mode pins maxNatSize (ds.toList.take k) (0, mkFEnv Env.empty) (k, fe) ∧
      PushChain Env.empty fe ∧ fe = mkFEnv (streamEnv (ds.toList.take k))
  | 0, _, _ => ⟨mkFEnv Env.empty, by simpa using DeclsRun.nil _, PushChain.refl _, rfl⟩
  | k + 1, hk, hm => by
    obtain ⟨fe, hrun, hchain, hfe⟩ := jobs_run_upto h k (by omega) (by omega)
    have hk' : k < ds.size := by omega
    have ht : Twin fe ((buildIndex ds).view k) := twin_at hk' hchain hfe
    have hjob := h k hk' (by omega)
    unfold recordJob at hjob
    split at hjob
    case isFalse => exact nomatch hjob
    rename_i hand
    rcases checkDeclStepC_twin (mode := mode) pins ht ds[k] { maxNatSize := maxNatSize } with
      ⟨e, -, h₂⟩ | ⟨a₁, a₂, s', h₁, h₂, L', Q', rfl, rfl⟩
    · rw [h₂] at hjob; exact nomatch hjob
    · have hpush := checkDeclStepC_pushes (pins := pins) mode fe ds[k] { maxNatSize := maxNatSize } _ s' h₁
      have hstep : declStep mode pins maxNatSize (k, fe) ds[k] = .ok (k + 1, FEnv.pushDelta L' Q' fe) := by
        unfold declStep
        simp only [hand, ↓reduceIte, h₁]
      have hL : ds.toList.take (k + 1) = ds.toList.take k ++ [ds[k]] := by
        rw [List.take_add_one]
        simp [Array.getElem?_eq_getElem hk']
      have hchain' := checkDeclStepC_push (pins := pins) mode hchain ds[k] { maxNatSize := maxNatSize } _ s' h₁
      have hfe' : FEnv.pushDelta L' Q' fe = mkFEnv (streamEnv (ds.toList.take (k + 1))) := by
        rw [hpush, hfe, pushDelta_mkFEnv, hL]
        congr 1
        simp [streamEnv, List.foldl_append]
      refine ⟨_, ?_, hchain', hfe'⟩
      rw [hL]; exact hrun.snoc mode hstep

/-- **The reject direction.** If every job before position `k` passes and job `k` fails with `e`,
the fold fails with `e` at position `k`. -/
theorem checkDecls_error_of_jobs {ds : Array Declaration} {k : Nat} (hk : k < ds.size)
    (hpre : ∀ j (hj : j < ds.size), j < k →
      recordJob mode pins maxNatSize (buildIndex ds) j ds[j] = .ok ())
    {e : CheckError} (hfail : recordJob mode pins maxNatSize (buildIndex ds) k ds[k] = .error e) :
    checkDecls mode pins maxNatSize ds = .error (e, k) := by
  obtain ⟨fe, hrun, hchain, hfe⟩ := jobs_run_upto hpre k (by omega) (Nat.le_refl _)
  have ht := twin_at hk hchain hfe
  -- the fold's step at `k` fails as the job does
  have hstep : declStep mode pins maxNatSize (k, fe) ds[k] = .error (e, k) := by
    unfold recordJob at hfail
    unfold declStep
    split
    case isFalse hand => simp only [hand, Bool.false_eq_true, ↓reduceIte] at hfail; cases hfail; rfl
    rename_i hand
    simp only [hand, ↓reduceIte] at hfail
    rcases checkDeclStepC_twin (mode := mode) pins ht ds[k] { maxNatSize := maxNatSize } with
      ⟨e', h₁, h₂⟩ | ⟨a₁, a₂, s', h₁, h₂, -⟩
    · rw [h₂] at hfail; cases hfail; simp only [h₁]
    · rw [h₂] at hfail; exact nomatch hfail
  have hsplit : ds.toList = ds.toList.take k ++ ds[k] :: ds.toList.drop (k + 1) := by
    conv => lhs; rw [← List.take_append_drop k ds.toList]
    rw [List.drop_eq_getElem_cons (by simpa using hk)]
    simp
  unfold checkDecls
  rw [← Array.foldlM_toList, hsplit, List.foldlM_append, hrun.foldlM]
  simp only [bind, Except.bind, List.foldlM_cons, hstep]

/-- The in-order walk over the jobs from position `k`: the first failing job decides. -/
def walkJobs (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat) (ds : Array Declaration)
    (I : StreamIndex) (k : Nat) : Except (CheckError × Nat) Unit :=
  if hk : k < ds.size then
    match recordJob mode pins maxNatSize I k ds[k] with
    | .ok () => walkJobs mode pins maxNatSize ds I (k + 1)
    | .error e => .error (e, k)
  else .ok ()
termination_by ds.size - k

theorem walkJobs_ok {ds : Array Declaration} {I : StreamIndex} :
    ∀ k, walkJobs mode pins maxNatSize ds I k = .ok () →
      ∀ j (hj : j < ds.size), k ≤ j → recordJob mode pins maxNatSize I j ds[j] = .ok () := by
  intro k
  induction h : ds.size - k generalizing k with
  | zero => intro _ j hj hkj; omega
  | succ n ih =>
    intro hw j hj hkj
    have hk : k < ds.size := by omega
    unfold walkJobs at hw
    simp only [hk, ↓reduceDIte] at hw
    split at hw
    · rename_i hok
      rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
      · exact hok
      · exact ih (k + 1) (by omega) hw j hj hlt
    · exact nomatch hw

theorem walkJobs_error {ds : Array Declaration} {I : StreamIndex} :
    ∀ k, (∀ j (hj : j < ds.size), j < k → recordJob mode pins maxNatSize I j ds[j] = .ok ()) →
      ∀ ε, walkJobs mode pins maxNatSize ds I k = .error ε →
        ∃ (hk : ε.2 < ds.size), (∀ j (hj : j < ds.size), j < ε.2 →
          recordJob mode pins maxNatSize I j ds[j] = .ok ()) ∧
          recordJob mode pins maxNatSize I ε.2 ds[ε.2] = .error ε.1 := by
  intro k
  induction h : ds.size - k generalizing k with
  | zero =>
    intro _ ε hw
    unfold walkJobs at hw
    simp only [show ¬ k < ds.size by omega, ↓reduceDIte] at hw
    exact nomatch hw
  | succ n ih =>
    intro hpre ε hw
    have hk : k < ds.size := by omega
    unfold walkJobs at hw
    simp only [hk, ↓reduceDIte] at hw
    split at hw
    · rename_i hok
      refine ih (k + 1) (by omega) ?_ ε hw
      intro j hj hjk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hjk) with hlt | rfl
      · exact hpre j hj hlt
      · exact hok
    · rename_i e he
      cases hw
      exact ⟨hk, hpre, he⟩

/-- **The in-order walk over the jobs is the fold's verdict**, error included. -/
theorem walkJobs_eq (ds : Array Declaration) :
    (walkJobs mode pins maxNatSize ds (buildIndex ds) 0).map (fun _ => streamEnv ds.toList) =
      checkDecls mode pins maxNatSize ds := by
  cases hw : walkJobs mode pins maxNatSize ds (buildIndex ds) 0 with
  | ok u =>
    rw [checkDecls_of_jobs fun k hk => walkJobs_ok 0 hw k hk (Nat.zero_le _)]
    rfl
  | error ε =>
    obtain ⟨hk, hpre, hfail⟩ := walkJobs_error 0 (fun _ _ h => absurd h (Nat.not_lt_zero _)) ε hw
    rw [checkDecls_error_of_jobs hk hpre hfail]
    rfl

end ConPastel.Par
