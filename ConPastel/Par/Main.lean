import ConPastel.Par.Decls

/-!
# The main program of the parallel checker, in one process

`parMainRun`: in an environment where the translated units `phase1`, `phase1Ok`, `jobCode`,
`verdictCode` and `revApp` are bound to values satisfying their certificates, the main declarations
(`parMainDecs`) of one process end, and the events they add satisfy `ProcOk`: the process writes
exactly `expectedOut`, and every report it makes is correct (`ReportOk`).
-/

namespace ConPastel.Par
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.SemanticsHOL
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString ConPastel.Translator ConPastel.Program
open ConPastel.Main

/-! ## What one process does -/

/-- The first phase on a process's input. -/
def phase1Of (io : ParIO) : Phase1 := phase1 (byteNats io.input)

/-- **What a process writes**: `rejected` if the first phase failed; nothing in a worker; in the
parent, the verdict on the table it read, or nothing (it aborts) if that is not a table of jobs. -/
def expectedOut (io : ParIO) : List (BitVec 8) :=
  if (phase1Of io).ok then
    if io.worker then []
    else match verdictCode (phase1Of io) (byteNats io.table) with
      | 0 => verdictBytes true
      | 1 => verdictBytes false
      | _ => []
  else verdictBytes false

/-- **The specification of one process's events.** -/
def ProcOk (io : ParIO) (evs : List HolIoEvent) : Prop :=
  writtenBytes evs = expectedOut io ∧ ∀ e ∈ evs, IsCall "report" e → ReportOk (phase1Of io) e

/-! ## The oracle on the other calls -/

theorem streamFfi_read : StreamFfi parOracle "read" (·.input) (fun st r => { st with input := r }) where
  ans st conf bytes h := by simp +decide [parOracle, h]
  get_set _ _ := rfl
  set_set _ _ _ := rfl
  ne := by decide

theorem streamFfi_results :
    StreamFfi parOracle "results" (·.table) (fun st r => { st with table := r }) where
  ans st conf bytes h := by simp +decide [parOracle, h]
  get_set _ _ := rfl
  set_set _ _ _ := rfl
  ne := by decide

theorem parOracle_write (st : ParIO) (conf bytes : List (BitVec 8)) :
    parOracle (.extCall (ofString "write")) st conf bytes = .ret st bytes := by
  simp +decide [parOracle]

theorem parOracle_spawn (st : ParIO) (conf bytes : List (BitVec 8)) (h : bytes.length = 9) :
    parOracle (.extCall (ofString "spawn")) st conf bytes =
      .ret st ((if st.worker then 1 else 0) :: bytes.drop 1) := by
  simp +decide [parOracle, h]

theorem parOracle_abort (st : ParIO) (conf bytes : List (BitVec 8)) :
    parOracle (.extCall (ofString "abort")) st conf bytes = .final .failed := by
  simp +decide [parOracle]

/-! ## Events -/

theorem writtenBytes_calls (n : String) (hn : ofString n ≠ ofString "write") :
    ∀ evs : List HolIoEvent, (∀ e ∈ evs, IsCall n e) → writtenBytes evs = []
  | [], _ => rfl
  | e :: evs, h => by
    have he : e.name ≠ .extCall (ofString "write") := by
      rw [h e (.head _)]; intro h'; exact hn (HolFfiName.extCall.inj h')
    simp only [writtenBytes, List.flatMap_cons, he, ite_false, List.nil_append] at *
    exact writtenBytes_calls n hn evs fun e he => h e (.tail _ he)

theorem writtenBytes_write (conf bytes : List (BitVec 8)) :
    writtenBytes [ffiEvent "write" conf bytes bytes] = conf := by
  simp [writtenBytes, ffiEvent]

theorem reports_calls (n : String) (hn : ofString n ≠ ofString "report") (P : Phase1)
    (evs : List HolIoEvent) (h : ∀ e ∈ evs, IsCall n e) : ∀ e ∈ evs, IsCall "report" e → ReportOk P e := by
  intro e he hr
  exact absurd ((h e he).symm.trans hr) fun h' => hn (HolFfiName.extCall.inj h')

theorem verdictBytes_eq (b : Bool) :
    (ofString (if b then "accepted\n" else "rejected\n")).explode = verdictBytes b := by
  cases b <;> decide

/-! ## Constructor checks -/

theorem tableOk_list (c : Namespace ModN ConN (Nat × Stamp)) (hc : HasListCons c) :
    TableOk [(ofString "::", 2), (ofString "[]", 0)] c := by
  intro k n h
  simp only [List.lookup] at h
  split at h
  · next heq => cases h; rw [beq_iff_eq] at heq; subst heq; exact ⟨_, hc.cons⟩
  · split at h
    · next heq => cases h; rw [beq_iff_eq] at heq; subst heq; exact ⟨_, hc.nil⟩
    · simp at h

theorem everyExp_list (c : Namespace ModN ConN (Nat × Stamp)) (hc : HasListCons c) (e : Exp)
    (h : conOk [(ofString "::", 2), (ofString "[]", 0)] e = true) : everyExp (oneConCheck c) e = true :=
  everyExp_of_conOk (tableOk_list c hc) e h

/-! ## Reading a stream into a list -/

/-- `revApp (fname [], [])`: the stream read by the loop `fname`, in order. -/
theorem runs_rev_loop {σ : Type} {o : HolOracle σ} {ffi fname : String} {get : σ → List (BitVec 8)}
    {set : σ → List (BitVec 8) → σ} (hO : StreamFfi o ffi get set)
    (E₁ Ec : SemEnv Value) (ℓ : Nat)
    (hbuf : nsLookup E₁.v (.short (ofString bufName)) = some (.loc true ℓ))
    (hc₁ : HasListCons E₁.c) (hcc : HasListCons Ec.c)
    (hlk : nsLookup Ec.v (.short (ofString fname)) = some (loopClosure E₁ ffi fname))
    (revName : String) (vr : Value)
    (hrev : nsLookup Ec.v (.short (ofString revName)) = some vr)
    (hr : Arrow (PAIR (LIST NAT) (LIST NAT)) (LIST NAT) revAppT vr)
    (h1 : ofString bufName ≠ ofString "acc") (h2 : ofString bufName ≠ ofString fname)
    (h3 : ofString fname ≠ ofString "acc")
    (s : State σ) (c d : BitVec 8) (hst : s.refs[ℓ]? = some (.w8array [c, d])) (hor : s.ffi.oracle = o) :
    ∃ refs' calls v,
      Runs s Ec [.app .opapp [var revName, .con none [.app .opapp [var fname, nilE], nilE]]]
        { s with
          refs := refs'
          ffi := { s.ffi with ffiState := set s.ffi.ffiState [], ioEvents := s.ffi.ioEvents ++ calls } }
        (.val [v]) ∧
      LIST NAT (byteNats (get s.ffi.ffiState)) v ∧ (∀ e ∈ calls, IsCall ffi e) ∧
      (∃ c' d', refs'[ℓ]? = some (.w8array [c', d'])) := by
  -- the loop
  have hargs := Runs.cons (Runs.con_nil s hcc) (Runs.var s Ec fname _ hlk)
  have happ : doOpApp [loopClosure E₁ ffi fname, .conv (some (.typeStamp nilC 1)) []] =
      some (recBodyEnv E₁ (loopFuns ffi fname) (ofString "acc") (.conv (some (.typeStamp nilC 1)) []),
        loopBody ffi fname) := by
    simp [doOpApp, loopClosure, loopFuns, findRecFun, recBodyEnv]
  obtain ⟨refs₁, calls, v, heval, hv, hcalls, c₁, d₁, hbuf₁⟩ :=
    loop_spec hO E₁ ℓ hbuf hc₁ h1 h2 h3 (get s.ffi.ffiState) [] _ rfl s c d hst hor rfl 0
  have hloop : Runs s Ec [.app .opapp [var fname, nilE]]
      { s with
        refs := refs₁
        ffi := { s.ffi with ffiState := set s.ffi.ffiState [], ioEvents := s.ffi.ioEvents ++ calls } }
      (.val [v]) :=
    Runs.app_opapp hargs happ ⟨(get s.ffi.ffiState).length + 0, 0, heval⟩
  let s₁ : State σ := { s with
    refs := refs₁
    ffi := { s.ffi with ffiState := set s.ffi.ffiState [], ioEvents := s.ffi.ioEvents ++ calls } }
  have hpair := Runs.con_none (args := [.app .opapp [var fname, nilE], nilE])
    (Runs.cons (Runs.con_nil s hcc) hloop)
  obtain ⟨vrev, rr, hrevRun, hvrev⟩ := Runs.app_returns
    (Runs.cons hpair (Runs.var s₁ Ec revName vr hrev))
    (hr ((byteNats (get s.ffi.ffiState)).reverse, []) _ ⟨v, _, by simpa using hv, rfl, rfl⟩)
  refine ⟨refs₁ ++ rr, calls, vrev, hrevRun, ?_, hcalls, c₁, d₁, refs_append_get hbuf₁ rr⟩
  simpa [revAppT, revApp_eq] using hvrev

/-! ## The dispatch after the first phase -/

/-- What a process with first phase `P` and script `io` writes. -/
def expectedOutP (P : Phase1) (io : ParIO) : List (BitVec 8) :=
  if P.ok then
    if io.worker then []
    else match verdictCode P (byteNats io.table) with
      | 0 => verdictBytes true
      | 1 => verdictBytes false
      | _ => []
  else verdictBytes false

theorem expectedOut_eq (io : ParIO) : expectedOut io = expectedOutP (phase1Of io) io := rfl

theorem runs_unit {σ : Type} (s : State σ) (env : SemEnv Value) :
    Runs s env [.con none []] s (.val [.conv none []]) :=
  Runs.con_none (args := []) ⟨0, 0, evaluate_nil_list _ _⟩

theorem ne_write : ofString "write" ≠ MlString.implode [] := by decide
theorem ne_spawn : ofString "spawn" ≠ MlString.implode [] := by decide
theorem ne_abort : ofString "abort" ≠ MlString.implode [] := by decide

section
variable {INVp : RefInv Phase1}

/-- What the dispatch needs of its environment. -/
structure DispatchEnv (okName jobCodeName verdictName revName : String) (P : Phase1)
    (E E₂ E₅ : SemEnv Value) (ℓ ℓj : Nat) (pv vok vjc vv vr : Value) : Prop where
  cons : HasListCons E.c
  cons₂ : HasListCons E₂.c
  buf : nsLookup E.v (.short (ofString bufName)) = some (.loc true ℓ)
  buf₂ : nsLookup E₂.v (.short (ofString bufName)) = some (.loc true ℓ)
  jb : nsLookup E.v (.short (ofString jbName)) = some (.loc true ℓj)
  p : nsLookup E.v (.short (ofString pName)) = some pv
  ok : nsLookup E.v (.short (ofString okName)) = some vok
  vd : nsLookup E.v (.short (ofString verdictName)) = some vv
  rev : nsLookup E.v (.short (ofString revName)) = some vr
  table : nsLookup E.v (.short (ofString readTableName)) = some (loopClosure E₂ "results" readTableName)
  work : nsLookup E.v (.short (ofString workName)) = some (workClosure E₅ jobCodeName)
  pinv : INVp P pv
  okinv : Arrow INVp BOOL phase1Ok vok
  vdinv : Arrow INVp (Arrow (LIST NAT) NAT) verdictCode vv
  revinv : Arrow (PAIR (LIST NAT) (LIST NAT)) (LIST NAT) revAppT vr
  wenv : WorkEnv (INVp := INVp) jobCodeName P E₅ ℓj pv vjc
  n_v : ∀ n ∈ [bufName, pName, verdictName, revName, readTableName], ofString n ≠ ofString "v"

theorem writtenBytes_nowrite :
    ∀ evs : List HolIoEvent, (∀ e ∈ evs, e.name ≠ .extCall (ofString "write")) → writtenBytes evs = []
  | [], _ => rfl
  | e :: evs, h => by
    simp only [writtenBytes, List.flatMap_cons, h e (.head _), ite_false, List.nil_append] at *
    exact writtenBytes_nowrite evs fun e he => h e (.tail _ he)

theorem isCall_ne {n m : String} {e : HolIoEvent} (h : IsCall n e) (hnm : ofString n ≠ ofString m) :
    e.name ≠ .extCall (ofString m) := by
  rw [h]; intro h'; exact hnm (HolFfiName.extCall.inj h')

/-- The parent's verdict on the table it read. -/
def parentOut (P : Phase1) (io : ParIO) : List (BitVec 8) :=
  match verdictCode P (byteNats io.table) with
  | 0 => verdictBytes true
  | 1 => verdictBytes false
  | _ => []

/-- **The parent**: read the table, write the verdict on it or abort. -/
theorem runs_parent {okName jobCodeName verdictName revName : String} {P : Phase1}
    {E E₂ E₅ : SemEnv Value} {ℓ ℓj : Nat} {pv vok vjc vv vr : Value}
    (h : DispatchEnv (INVp := INVp) okName jobCodeName verdictName revName P E E₂ E₅ ℓ ℓj pv vok vjc vv vr)
    (s : State ParIO) (c d : BitVec 8) (hst : s.refs[ℓ]? = some (.w8array [c, d]))
    (hor : s.ffi.oracle = parOracle) :
    ∃ s' r evs, Runs s E [parentBody verdictName revName] s' r ∧ Ended r ∧
      s'.ffi.ioEvents = s.ffi.ioEvents ++ evs ∧ writtenBytes evs = parentOut P s.ffi.ffiState ∧
      ∀ e ∈ evs, e.name ≠ .extCall (ofString "report") := by
  -- the table
  obtain ⟨refs₁, calls, lv, hX, hlv, hcalls, c₁, d₁, hbuf₁⟩ :=
    runs_rev_loop streamFfi_results E₂ E ℓ h.buf₂ h.cons₂ h.cons h.table revName vr h.rev h.revinv
      (by decide) (by decide) (by decide) s c d hst hor
  let s₁ : State ParIO := { s with
    refs := refs₁
    ffi := { s.ffi with
      ffiState := { s.ffi.ffiState with table := [] }
      ioEvents := s.ffi.ioEvents ++ calls } }
  -- `verdictCode p`
  obtain ⟨fv, rf, hfRun, hf⟩ := Runs.app_returns
    (Runs.cons (Runs.var s₁ E pName pv h.p) (Runs.var s₁ E verdictName vv h.vd)) (h.vdinv P pv h.pinv)
  obtain ⟨cv, rc, hcRun, hcv⟩ := Runs.app_returns (Runs.cons hX hfRun) (hf _ lv hlv)
  let code := verdictCode P (byteNats s.ffi.ffiState.table)
  have hcv' : cv = .litv (.intLit code) := hcv
  let s₂ : State ParIO := { s₁ with refs := s₁.refs ++ rf ++ rc }
  have hbuf₂ : s₂.refs[ℓ]? = some (.w8array [c₁, d₁]) := refs_append_get (refs_append_get hbuf₁ rf) rc
  have hor₂ : s₂.ffi.oracle = parOracle := hor
  let Ev : SemEnv Value := { E with v := nsOptBind (some (ofString "v")) cv E.v }
  have hEv_v : nsLookup Ev.v (.short (ofString "v")) = some (.litv (.intLit code)) := by
    simp [Ev, nsOptBind, nsLookup_nsBind_short, hcv']
  have hEv_buf : nsLookup Ev.v (.short (ofString bufName)) = some (.loc true ℓ) := by
    have hn := h.n_v bufName (by simp)
    simp [Ev, nsOptBind, nsLookup_nsBind_short, hn, h.buf]
  have hnr : ∀ e ∈ calls, e.name ≠ .extCall (ofString "report") :=
    fun e he => isCall_ne (hcalls e he) (by decide)
  have hnw : writtenBytes calls = [] :=
    writtenBytes_nowrite calls fun e he => isCall_ne (hcalls e he) (by decide)
  have hif : ∀ n, Runs s₂ Ev [intEq (var "v") n] s₂ (.val [boolValue (decide (code = n))]) :=
    fun n => ⟨0, 0, eval_intEq _ Ev "v" code n hEv_v⟩
  -- writing a verdict
  have hwrite : ∀ b : Bool, Runs s₂ Ev [ffiCall "write" (if b then "accepted\n" else "rejected\n") bufName]
      { s₂ with
        refs := s₂.refs.set ℓ (.w8array [c₁, d₁])
        ffi := { s₂.ffi with
          ffiState := s₂.ffi.ffiState
          ioEvents := s₂.ffi.ioEvents ++
            [ffiEvent "write" (ofString (if b then "accepted\n" else "rejected\n")).explode [c₁, d₁] [c₁, d₁]] } }
      (.val [.conv none []]) := fun b =>
    Runs.ffi_ret Ev s₂ "write" bufName _ _ ℓ [c₁, d₁] [c₁, d₁] _ (fun ck => eval_strLit _ _ _) hEv_buf
      hbuf₂ ne_write (by rw [hor₂]; exact parOracle_write _ _ _) rfl
  have hevs₂ : s₂.ffi.ioEvents = s.ffi.ioEvents ++ calls := rfl
  have hlet : ∀ {s' : State ParIO} {r : Result (List Value) Value},
      Runs s₂ Ev [.if_ (intEq (var "v") 0) (ffiCall "write" "accepted\n" bufName)
        (.if_ (intEq (var "v") 1) (ffiCall "write" "rejected\n" bufName) (ffiCall "abort" "" bufName))] s' r →
      Ended r → Runs s E [parentBody verdictName revName] s' r := by
    intro s' r hr he
    exact Runs.let_ hcRun hr he.not_timeout
  by_cases h0 : code = 0
  · have hR := Runs.if_ (hif 0) (by simp only [h0, decide_true, ite_true]; exact hwrite true) (by simp)
      (e₂ := ffiCall "write" "accepted\n" bufName)
      (e₃ := .if_ (intEq (var "v") 1) (ffiCall "write" "rejected\n" bufName) (ffiCall "abort" "" bufName))
    refine ⟨_, _, calls ++ [ffiEvent "write" (ofString "accepted\n").explode [c₁, d₁] [c₁, d₁]],
      hlet hR (.inl rfl), .inl rfl, by simp [s₂, s₁], ?_, ?_⟩
    · rw [writtenBytes_append, hnw, writtenBytes_write]
      simp only [parentOut]; rw [show verdictCode P (byteNats s.ffi.ffiState.table) = 0 from h0]
      exact verdictBytes_eq true
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hnr e he
      · simp only [List.mem_singleton] at he; subst he
        exact fun h' => absurd (HolFfiName.extCall.inj h') (by decide)
  by_cases h1 : code = 1
  · have hR := Runs.if_ (hif 0) (by
        simp only [h0, decide_false, Bool.false_eq_true, ite_false]
        exact Runs.if_ (hif 1) (by simp only [h1, decide_true, ite_true]; exact hwrite false) (by simp))
      (by simp) (e₂ := ffiCall "write" "accepted\n" bufName)
      (e₃ := .if_ (intEq (var "v") 1) (ffiCall "write" "rejected\n" bufName) (ffiCall "abort" "" bufName))
    refine ⟨_, _, calls ++ [ffiEvent "write" (ofString "rejected\n").explode [c₁, d₁] [c₁, d₁]],
      hlet hR (.inl rfl), .inl rfl, by simp [s₂, s₁], ?_, ?_⟩
    · rw [writtenBytes_append, hnw, writtenBytes_write]
      simp only [parentOut]; rw [show verdictCode P (byteNats s.ffi.ffiState.table) = 1 from h1]
      exact verdictBytes_eq false
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hnr e he
      · simp only [List.mem_singleton] at he; subst he
        exact fun h' => absurd (HolFfiName.extCall.inj h') (by decide)
  · have hab := Runs.ffi_final Ev s₂ "abort" bufName (strE "") _ ℓ [c₁, d₁] .failed
      (fun ck => eval_strLit _ _ _) hEv_buf hbuf₂ ne_abort (by rw [hor₂]; exact parOracle_abort _ _ _)
    have hR := Runs.if_ (hif 0) (by
        simp only [h0, decide_false, Bool.false_eq_true, ite_false]
        exact Runs.if_ (hif 1) (by simp only [h1, decide_false, Bool.false_eq_true, ite_false]; exact hab)
          (by simp))
      (by simp) (e₂ := ffiCall "write" "accepted\n" bufName)
      (e₃ := .if_ (intEq (var "v") 1) (ffiCall "write" "rejected\n" bufName) (ffiCall "abort" "" bufName))
    refine ⟨_, _, calls, hlet hR (.inr ⟨_, rfl⟩), .inr ⟨_, rfl⟩, hevs₂, ?_, hnr⟩
    · rw [hnw]; simp only [parentOut]
      split
      · next hc => exact absurd hc h0
      · next hc => exact absurd hc h1
      · rfl

/-- **The dispatch**: the three roles of a process. -/
theorem runs_dispatch {okName jobCodeName verdictName revName : String} {P : Phase1}
    {E E₂ E₅ : SemEnv Value} {ℓ ℓj : Nat} {pv vok vjc vv vr : Value}
    (h : DispatchEnv (INVp := INVp) okName jobCodeName verdictName revName P E E₂ E₅ ℓ ℓj pv vok vjc vv vr)
    (s : State ParIO) (c d : BitVec 8) (hst : s.refs[ℓ]? = some (.w8array [c, d]))
    (hjb : s.refs[ℓj]? = some (.w8array (List.replicate 9 0))) (hor : s.ffi.oracle = parOracle) :
    ∃ s' r evs, Runs s E [dispatch okName verdictName revName] s' r ∧ Ended r ∧
      s'.ffi.ioEvents = s.ffi.ioEvents ++ evs ∧
      writtenBytes evs = expectedOutP P s.ffi.ffiState ∧
      ∀ e ∈ evs, IsCall "report" e → ReportOk P e := by
  -- `phase1Ok p`
  obtain ⟨bv, rok, hokRun, hbv⟩ := Runs.app_returns
    (Runs.cons (Runs.var s E pName pv h.p) (Runs.var s E okName vok h.ok)) (h.okinv P pv h.pinv)
  have hbv' : bv = boolValue P.ok := hbv
  subst hbv'
  let s₁ : State ParIO := { s with refs := s.refs ++ rok }
  have hst₁ : s₁.refs[ℓ]? = some (.w8array [c, d]) := refs_append_get hst rok
  have hjb₁ : s₁.refs[ℓj]? = some (.w8array (List.replicate 9 0)) := refs_append_get hjb rok
  unfold dispatch
  cases hP : P.ok
  · -- the first phase failed: `rejected`
    have hw := Runs.ffi_ret E s₁ "write" bufName (strE "rejected\n") _ ℓ [c, d] [c, d] s.ffi.ffiState
      (fun ck => eval_strLit _ _ _) h.buf hst₁ ne_write (by rw [hor]; exact parOracle_write _ _ _) rfl
    refine ⟨_, _, [ffiEvent "write" (ofString "rejected\n").explode [c, d] [c, d]],
      Runs.if_ (hP ▸ hokRun) (by simp only [Bool.false_eq_true, ite_false]; exact hw) (by simp),
      .inl rfl, rfl, ?_, ?_⟩
    · rw [writtenBytes_write]; simp [expectedOutP, hP]; decide
    · intro e he hr
      simp only [List.mem_singleton] at he; subst he
      exact absurd hr (by intro h'; exact absurd (HolFfiName.extCall.inj h') (by decide))
  · -- spawn
    have hlt : ℓj < s₁.refs.length := by
      rcases Nat.lt_or_ge ℓj s₁.refs.length with h' | h'
      · exact h'
      · simp [List.getElem?_eq_none h'] at hjb₁
    let w : BitVec 8 := if s.ffi.ffiState.worker then 1 else 0
    let jb₁ : List (BitVec 8) := w :: List.replicate 8 0
    have hsp := Runs.ffi_ret E s₁ "spawn" jbName (strE "") _ ℓj (List.replicate 9 0) jb₁ s.ffi.ffiState
      (fun ck => eval_strLit _ _ _) h.jb hjb₁ ne_spawn
      (by rw [hor]; exact parOracle_spawn _ _ _ (by simp)) (by simp [jb₁])
    let evS := ffiEvent "spawn" (ofString "").explode (List.replicate 9 0) jb₁
    let s₂ : State ParIO := { s₁ with
      refs := s₁.refs.set ℓj (.w8array jb₁)
      ffi := { s₁.ffi with ffiState := s.ffi.ffiState, ioEvents := s₁.ffi.ioEvents ++ [evS] } }
    have hjb₂ : s₂.refs[ℓj]? = some (.w8array jb₁) := List.getElem?_set_self hlt
    have hst₂ : s₂.refs[ℓ]? = some (.w8array [c, d]) := by
      by_cases hl : ℓ = ℓj
      · subst hl; rw [hjb₁] at hst₁; cases hst₁
      · simp only [s₂]; rw [List.getElem?_set_ne (Ne.symm hl)]; exact hst₁
    have htest : Runs s₂ E [.app .equality [.app .aw8sub [var jbName, .lit (.intLit 0)], .lit (.word8 0)]]
        s₂ (.val [boolValue (decide (w = 0))]) :=
      ⟨0, 0, eval_test0' E jbName ℓj h.jb { s₂ with clock := 0 } (List.replicate 8 0) w hjb₂⟩
    have hS : IsCall "spawn" evS := rfl
    cases hW : s.ffi.ffiState.worker
    · -- the parent
      have hw0 : decide (w = 0) = true := by simp [w, hW]
      obtain ⟨s', r, evs, hrun, hend, hevs, hwb, hnr⟩ := runs_parent h s₂ c d hst₂ hor
      refine ⟨s', r, evS :: evs, ?_, hend, ?_, ?_, ?_⟩
      · refine Runs.if_ (hP ▸ hokRun) ?_ hend.not_timeout
        simp only [ite_true]
        refine Runs.let_ hsp (Runs.if_ htest ?_ hend.not_timeout) hend.not_timeout
        rw [hw0]; simp only [ite_true]; exact hrun
      · rw [hevs]; simp [s₂, s₁]
      · have h1 : writtenBytes [evS] = [] := writtenBytes_nowrite _ (by
          intro e he; simp only [List.mem_singleton] at he; subst he; exact isCall_ne hS (by decide))
        rw [show evS :: evs = [evS] ++ evs from rfl, writtenBytes_append, h1, List.nil_append, hwb]
        simp [expectedOutP, hP, hW, parentOut, s₂]
      · intro e he hr
        rcases List.mem_cons.mp he with rfl | he
        · exact absurd hr (isCall_ne hS (by decide))
        · exact absurd hr (hnr e he)
    · -- a worker
      have hw0 : decide (w = 0) = false := by simp [w, hW]
      obtain ⟨s', r, evs, hrun, hend, hevs, hor', hall⟩ :=
        work_spec h.wenv (.conv none []) s₂.ffi.ffiState.claims s₂ jb₁ (by simp [jb₁]) hjb₂ hor rfl
      have happ : doOpApp [workClosure E₅ jobCodeName, .conv none []] =
          some (workBodyEnv E₅ jobCodeName (.conv none []), workBody jobCodeName) := by
        simp [doOpApp, workClosure, workFuns, findRecFun, recBodyEnv, workBodyEnv]
      have hcall : Runs s₂ E [.app .opapp [var workName, .con none []]] s' r :=
        Runs.app_opapp_any (Runs.cons (runs_unit s₂ E) (Runs.var s₂ E workName _ h.work)) happ hrun
          hend.not_timeout
      refine ⟨s', r, evS :: evs, ?_, hend, ?_, ?_, ?_⟩
      · refine Runs.if_ (hP ▸ hokRun) ?_ hend.not_timeout
        simp only [ite_true]
        refine Runs.let_ hsp (Runs.if_ htest ?_ hend.not_timeout) hend.not_timeout
        rw [hw0]; simp only [Bool.false_eq_true, ite_false]; exact hcall
      · rw [hevs]; simp [s₂, s₁]
      · have : ∀ e ∈ evS :: evs, IsCall "spawn" e ∨ IsCall "claim" e ∨ IsCall "report" e := by
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact .inl hS
          · rcases hall e he with h' | ⟨h', -⟩
            · exact .inr (.inl h')
            · exact .inr (.inr h')
        simp only [expectedOutP, hP, hW, ite_true]
        refine writtenBytes_nowrite _ fun e he => ?_
        rcases this e he with h' | h' | h'
        · exact isCall_ne h' (by decide)
        · exact isCall_ne h' (by decide)
        · exact isCall_ne h' (by decide)
      · intro e he hr
        rcases List.mem_cons.mp he with rfl | he
        · exact absurd (hS.symm.trans hr) (by intro h'; exact absurd (HolFfiName.extCall.inj h') (by decide))
        · rcases hall e he with h' | ⟨-, h'⟩
          · exact absurd (h'.symm.trans hr) (by intro h''; exact absurd (HolFfiName.extCall.inj h'') (by decide))
          · exact h'
end

end ConPastel.Par
