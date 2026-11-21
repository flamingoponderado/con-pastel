import ConPastel.Par.Main

/-!
# The main declarations of one process

`parMainRun`: the seven main declarations (`parMainDecs`) run in one process, from an environment
binding the translated units, end, and add events satisfying `ProcOk`.
-/

namespace ConPastel.Par
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.SemanticsHOL
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString ConPastel.Translator ConPastel.Program
open ConPastel.Main

/-- The names the main declarations bind or use locally. -/
def mainNames : List String :=
  [bufName, readAllName, readTableName, pName, jbName, workName, "v", "c", "u", "acc"]

/-- An environment extended by one binding. -/
def ext1 (n : String) (x : Value) (E : SemEnv Value) : SemEnv Value :=
  extendDecEnv { v := .bind [(ofString n, x)] [], c := nsEmpty } E

theorem ext1_hit (n : String) (x : Value) (E : SemEnv Value) :
    nsLookup (ext1 n x E).v (.short (ofString n)) = some x :=
  lookup_extend_hit _ _ [] E

theorem ext1_miss (n m : String) (x : Value) (E : SemEnv Value) (h : ofString m ≠ ofString n) :
    nsLookup (ext1 n x E).v (.short (ofString m)) = nsLookup E.v (.short (ofString m)) :=
  lookup_extend_miss _ _ _ (by simp [h])

theorem ext1_c (n : String) (x : Value) (E : SemEnv Value) : (ext1 n x E).c = E.c := by
  simp [ext1, extendDecEnv, nsAppend_nsEmpty]

theorem eval_alloc9 {σ : Type} (s : State σ) (env : SemEnv Value) :
    evaluate s env [.app .aw8alloc [.lit (.intLit 9), .lit (.word8 0)]] =
      ({ s with refs := s.refs ++ [.w8array (List.replicate 9 0)] }, .val [.loc true s.refs.length]) := by
  simp [evaluate, fixClock, getOpClass, headValue, Flapjack.holHd, doApp, doAppNumericCore,
    doAppBasic, storeAlloc, listResult]

theorem dletrec_one (s : State σ) (E : SemEnv Value) (f x : String) (body : Exp)
    (hcon : everyExp (oneConCheck E.c) body = true) :
    DeclsRun s E [.dletrec Flapjack.Misc.Location.unknownLoc [(ofString f, ofString x, body)]] s
      { v := .bind [(ofString f, .recclosure E [(ofString f, ofString x, body)] (ofString f))] [], c := nsEmpty } := by
  have := DeclsRun.dletrec (loc := Flapjack.Misc.Location.unknownLoc) s (env := E)
    (funs := [(ofString f, ofString x, body)]) (by simp) (by simp [hcon])
  simpa [buildRecEnv, nsEmpty] using this

theorem dlet_one {σ : Type} {s s₁ : State σ} {E : SemEnv Value} {n : String} {e : Exp} {v : Value}
    (hcon : everyExp (oneConCheck E.c) e = true) (h : Runs s E [e] s₁ (.val [v])) :
    DeclsRun s E [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString n)) e] s₁
      { v := .bind [(ofString n, v)] [], c := nsEmpty } := by
  have := DeclsRun.dlet (loc := Flapjack.Misc.Location.unknownLoc) (x := ofString n) hcon h
  simpa [alistToNs] using this

section
variable {INVp : RefInv Phase1}

/-- **The main declarations of one process.** -/
theorem parMainRun (p1N okN jcN vN revN : String) (E : SemEnv Value) (v1 vok vjc vv vr : Value)
    (h1 : nsLookup E.v (.short (ofString p1N)) = some v1) (c1 : Arrow (LIST NAT) INVp phase1 v1)
    (hok : nsLookup E.v (.short (ofString okN)) = some vok) (cok : Arrow INVp BOOL phase1Ok vok)
    (hjc : nsLookup E.v (.short (ofString jcN)) = some vjc)
    (cjc : Arrow INVp (Arrow (LIST NAT) NAT) jobCode vjc)
    (hvd : nsLookup E.v (.short (ofString vN)) = some vv)
    (cvd : Arrow INVp (Arrow (LIST NAT) NAT) verdictCode vv)
    (hrev : nsLookup E.v (.short (ofString revN)) = some vr)
    (crev : Arrow (PAIR (LIST NAT) (LIST NAT)) (LIST NAT) revAppT vr)
    (hlist : HasListCons E.c)
    (hfresh : ∀ n ∈ [p1N, okN, jcN, vN, revN], ∀ m ∈ mainNames, ofString n ≠ ofString m)
    (s : State ParIO) (hor : s.ffi.oracle = parOracle) :
    ∃ s' r evs, DeclsEnd s E (parMainDecs p1N okN jcN vN revN) s' r ∧ DecEnded r ∧
      s'.ffi.ioEvents = s.ffi.ioEvents ++ evs ∧ ProcOk s.ffi.ffiState evs := by
  have fr : ∀ n ∈ [p1N, okN, jcN, vN, revN], ∀ m ∈ mainNames, ofString n ≠ ofString m := hfresh
  have f1 := fun m hm => fr p1N (by simp) m hm
  have fok := fun m hm => fr okN (by simp) m hm
  have fjc := fun m hm => fr jcN (by simp) m hm
  have fvd := fun m hm => fr vN (by simp) m hm
  have frev := fun m hm => fr revN (by simp) m hm
  have tbl : ∀ (c : Namespace ModN ConN (Nat × Stamp)), HasListCons c → ∀ e,
      conOk [(ofString "::", 2), (ofString "[]", 0)] e = true → everyExp (oneConCheck c) e = true :=
    fun c hc e he => everyExp_list c hc e he
  let io := s.ffi.ffiState
  -- 1. buf
  let ℓ := s.refs.length
  let s₁ : State ParIO := { s with refs := s.refs ++ [.w8array [0, 0]] }
  have d₁ := dlet_one (n := bufName) (s := s) (s₁ := s₁) (E := E)
    (everyExp_of_conOk (tbl := []) (fun _ _ h => by simp at h) _ conOk_alloc)
    ⟨0, 0, eval_alloc { s with clock := 0 } E⟩
  let E₁ := ext1 bufName (.loc true ℓ) E
  have hc₁ : HasListCons E₁.c := by rw [ext1_c]; exact hlist
  -- 2. readAll
  have d₂ := dletrec_one s₁ E₁ readAllName "acc" (loopBody "read" readAllName)
    (tbl _ hc₁ _ (by decide))
  let E₂ := ext1 readAllName (loopClosure E₁ "read" readAllName) E₁
  have hc₂ : HasListCons E₂.c := by rw [ext1_c]; exact hc₁
  -- 3. readTable
  have d₃ := dletrec_one s₁ E₂ readTableName "acc" (loopBody "results" readTableName)
    (tbl _ hc₂ _ (by decide))
  let E₃ := ext1 readTableName (loopClosure E₂ "results" readTableName) E₂
  have hc₃ : HasListCons E₃.c := by rw [ext1_c]; exact hc₂
  -- 4. p = phase1 (the input)
  have hbuf₁ : nsLookup E₁.v (.short (ofString bufName)) = some (.loc true ℓ) := ext1_hit _ _ _
  have hst₁ : s₁.refs[ℓ]? = some (.w8array [0, 0]) := by simp [s₁, ℓ]
  have hlkRA : nsLookup E₃.v (.short (ofString readAllName)) = some (loopClosure E₁ "read" readAllName) := by
    rw [ext1_miss _ _ _ _ (by decide)]; exact ext1_hit _ _ _
  have hrev₃ : nsLookup E₃.v (.short (ofString revN)) = some vr := by
    rw [ext1_miss _ _ _ _ (frev _ (by simp [mainNames])), ext1_miss _ _ _ _ (frev _ (by simp [mainNames])),
      ext1_miss _ _ _ _ (frev _ (by simp [mainNames]))]; exact hrev
  have h1₃ : nsLookup E₃.v (.short (ofString p1N)) = some v1 := by
    rw [ext1_miss _ _ _ _ (f1 _ (by simp [mainNames])), ext1_miss _ _ _ _ (f1 _ (by simp [mainNames])),
      ext1_miss _ _ _ _ (f1 _ (by simp [mainNames]))]; exact h1
  obtain ⟨refsI, reads, lv, hX, hlv, hreads, cI, dI, hbufI⟩ :=
    runs_rev_loop streamFfi_read E₁ E₃ ℓ hbuf₁ hc₁ hc₃ hlkRA revN vr hrev₃ crev
      (by decide) (by decide) (by decide) s₁ 0 0 hst₁ hor
  let sI : State ParIO := { s₁ with
    refs := refsI
    ffi := { s₁.ffi with
      ffiState := { s₁.ffi.ffiState with input := [] }
      ioEvents := s₁.ffi.ioEvents ++ reads } }
  let P := phase1 (byteNats io.input)
  obtain ⟨pv, rp, hpRun, hpv⟩ := Runs.app_returns (Runs.cons hX (Runs.var sI E₃ p1N v1 h1₃)) (c1 _ lv hlv)
  let s₂ : State ParIO := { sI with refs := sI.refs ++ rp }
  have d₄ := dlet_one (n := pName) (E := E₃) (tbl _ hc₃ _ (by simp +decide [conOk, conOkList, conHeadOk, nilE, var]))
    hpRun
  let E₄ := ext1 pName pv E₃
  have hc₄ : HasListCons E₄.c := by rw [ext1_c]; exact hc₃
  -- 5. jb
  let ℓj := s₂.refs.length
  let s₃ : State ParIO := { s₂ with refs := s₂.refs ++ [.w8array (List.replicate 9 0)] }
  have d₅ := dlet_one (n := jbName) (s := s₂) (s₁ := s₃) (E := E₄)
    (everyExp_of_conOk (tbl := []) (fun _ _ h => by simp at h) _ (by decide))
    ⟨0, 0, eval_alloc9 { s₂ with clock := 0 } E₄⟩
  let E₅ := ext1 jbName (.loc true ℓj) E₄
  have hc₅ : HasListCons E₅.c := by rw [ext1_c]; exact hc₄
  -- 6. work
  have d₆ := dletrec_one s₃ E₅ workName "u" (workBody jcN)
    (tbl _ hc₅ _ (by
      simp +decide [workBody, conOk, conOkList, conHeadOk, jbBytes, consE, nilE, jbByte, ffiCall, intEq,
        strE, var]))
  let E₆ := ext1 workName (workClosure E₅ jcN) E₅
  have hc₆ : HasListCons E₆.c := by rw [ext1_c]; exact hc₅
  -- 7. the dispatch
  have mm : ∀ m ∈ [bufName, readAllName, readTableName, pName, jbName, workName], m ∈ mainNames := by
    intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mainNames]
  -- a unit's name is not bound by the main declarations
  have unitLk : ∀ n x, (∀ m ∈ mainNames, ofString n ≠ ofString m) →
      nsLookup E.v (.short (ofString n)) = some x → nsLookup E₆.v (.short (ofString n)) = some x := by
    intro n x hn hx
    simp only [E₆, E₅, E₄, E₃, E₂, E₁]
    rw [ext1_miss _ _ _ _ (hn _ (mm _ (by simp))), ext1_miss _ _ _ _ (hn _ (mm _ (by simp))),
      ext1_miss _ _ _ _ (hn _ (mm _ (by simp))), ext1_miss _ _ _ _ (hn _ (mm _ (by simp))),
      ext1_miss _ _ _ _ (hn _ (mm _ (by simp))), ext1_miss _ _ _ _ (hn _ (mm _ (by simp)))]
    exact hx
  have hd : DispatchEnv (INVp := INVp) okN jcN vN revN P E₆ E₂ E₅ ℓ ℓj pv vok vjc vv vr := {
    cons := hc₆
    cons₂ := hc₂
    buf := by
      simp only [E₆, E₅, E₄, E₃, E₂, E₁]
      rw [ext1_miss _ _ _ _ (by decide), ext1_miss _ _ _ _ (by decide), ext1_miss _ _ _ _ (by decide),
        ext1_miss _ _ _ _ (by decide), ext1_miss _ _ _ _ (by decide), ext1_hit]
    buf₂ := by simp only [E₂, E₁]; rw [ext1_miss _ _ _ _ (by decide), ext1_hit]
    jb := by simp only [E₆, E₅]; rw [ext1_miss _ _ _ _ (by decide), ext1_hit]
    p := by simp only [E₆, E₅, E₄]; rw [ext1_miss _ _ _ _ (by decide), ext1_miss _ _ _ _ (by decide), ext1_hit]
    ok := unitLk okN vok fok hok
    vd := unitLk vN vv fvd hvd
    rev := unitLk revN vr frev hrev
    table := by
      simp only [E₆, E₅, E₄, E₃]
      rw [ext1_miss _ _ _ _ (by decide), ext1_miss _ _ _ _ (by decide), ext1_miss _ _ _ _ (by decide), ext1_hit]
    work := ext1_hit _ _ _
    pinv := hpv
    okinv := cok
    vdinv := cvd
    revinv := crev
    wenv := {
      jb := ext1_hit _ _ _
      p := by simp only [E₅, E₄]; rw [ext1_miss _ _ _ _ (by decide), ext1_hit]
      jc := by
        simp only [E₅, E₄, E₃, E₂, E₁]
        rw [ext1_miss _ _ _ _ (fjc _ (mm _ (by simp))), ext1_miss _ _ _ _ (fjc _ (mm _ (by simp))),
          ext1_miss _ _ _ _ (fjc _ (mm _ (by simp))), ext1_miss _ _ _ _ (fjc _ (mm _ (by simp))),
          ext1_miss _ _ _ _ (fjc _ (mm _ (by simp)))]
        exact hjc
      pinv := hpv
      jinv := cjc
      cons := hc₅
      n_u := fjc "u" (by simp [mainNames])
      n_w := fjc workName (by simp [mainNames]) }
    n_v := by
      intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      · exact fvd "v" (by simp [mainNames])
      · exact frev "v" (by simp [mainNames])
      · decide }
  have hstD : s₃.refs[ℓ]? = some (.w8array [cI, dI]) := by
    simp only [s₃, s₂]; exact refs_append_get (refs_append_get hbufI rp) _
  have hjbD : s₃.refs[ℓj]? = some (.w8array (List.replicate 9 0)) := by simp [s₃, ℓj]
  obtain ⟨s', r, evs, hrun, hend, hevs, hwb, hrep⟩ := runs_dispatch hd s₃ cI dI hstD hjbD hor
  obtain ⟨r', d₇, hr', -⟩ := DeclsEnd.dlet_ended (loc := Flapjack.Misc.Location.unknownLoc)
    (tbl _ hc₆ _ (by
      simp +decide [dispatch, parentBody, conOk, conOkList, conHeadOk, nilE, ffiCall, intEq, strE, var]))
    hrun hend
  have hD := DeclsEnd.cons d₁ (DeclsEnd.cons d₂ (DeclsEnd.cons d₃ (DeclsEnd.cons d₄ (DeclsEnd.cons d₅
    (DeclsEnd.cons d₆ d₇ hr') (hr'.combine _)) ((hr'.combine _).combine _)) (((hr'.combine _).combine _).combine _))
    ((((hr'.combine _).combine _).combine _).combine _)) (((((hr'.combine _).combine _).combine _).combine _).combine _)
  refine ⟨s', _, reads ++ evs, hD, (((((hr'.combine _).combine _).combine _).combine _).combine _).combine _, ?_, ?_, ?_⟩
  · rw [hevs]; simp [s₃, s₂, sI, s₁]
  · have hr0 : writtenBytes reads = [] := writtenBytes_nowrite _ fun e he => isCall_ne (hreads e he) (by decide)
    rw [writtenBytes_append, hr0, List.nil_append, hwb]
    rfl
  · intro e he hr
    rcases List.mem_append.mp he with he | he
    · exact absurd hr (isCall_ne (hreads e he) (by decide))
    · exact hrep e he hr
end

end ConPastel.Par
