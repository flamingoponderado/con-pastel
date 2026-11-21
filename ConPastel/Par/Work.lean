import ConPastel.Par.Ffi
import ConPastel.Par.Entry

/-!
# The worker loop

`work_spec`: run in a process whose FFI is `parOracle`, the worker loop claims job indices and
reports each one's code, `runJob P k` for the index `k` it was handed (`ReportOk`), until it reports
`3` (no such job) or the claims run out (an FFI failure). It adds only `claim` and `report` events.
-/

namespace ConPastel.Par
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString ConPastel.Translator ConPastel.Main

/-! ## What a report must say -/

/-- The configuration of a report of code `c`. -/
def codeConf (c : Nat) : List (BitVec 8) :=
  (ofString (if c = 3 then "3" else if c = 1 then "1" else "2")).explode

/-- The index a report event is about: bytes 1 to 8 of its buffer, little-endian. -/
def reportIndex (e : HolIoEvent) : Nat := decodeLE (byteNats ((e.bytes.map Prod.fst).drop 1))

/-- **A correct report**: its configuration is the code of the job at its index. -/
def ReportOk (P : Phase1) (e : HolIoEvent) : Prop := e.configuration = codeConf (runJob P (reportIndex e))

/-! ## Pure pieces -/

theorem eval_consE {σ : Type} (s : State σ) (env : SemEnv Value) (hc : HasListCons env.c)
    (h t : Exp) (hv tv : Value) (hh : evaluate s env [h] = (s, .val [hv]))
    (ht : evaluate s env [t] = (s, .val [tv])) :
    evaluate s env [consE h t] = (s, .val [.conv (some (.typeStamp consC 1)) [hv, tv]]) := by
  have hargs : evaluate s env [t, h] = (s, .val [tv, hv]) := evaluate_cons_val ht hh
  have hlk : nsLookup env.c (.short (ofString "::")) = some (2, .typeStamp consC 1) := hc.cons
  unfold consE
  rw [evaluate]
  simp [doConCheck, hlk, hargs, buildConv]

theorem eval_nilE {σ : Type} (s : State σ) (env : SemEnv Value) (hc : HasListCons env.c) :
    evaluate s env [nilE] = (s, .val [.conv (some (.typeStamp nilC 1)) []]) := by
  have hl : nsLookup env.c (.short (ofString "[]")) = some (0, .typeStamp nilC 1) := hc.nil
  unfold nilE
  rw [evaluate]
  simp [doConCheck, hl, buildConv, evaluate_nil_list]

/-- The value of a list of numbers. -/
def natListV : List Nat → Value
  | [] => .conv (some (.typeStamp nilC 1)) []
  | n :: l => .conv (some (.typeStamp consC 1)) [.litv (.intLit n), natListV l]

theorem LIST_natListV : ∀ l : List Nat, LIST NAT l (natListV l)
  | [] => rfl
  | n :: l => ⟨_, _, rfl, LIST_natListV l, rfl⟩

/-- `[w2n jb[1], …, w2n jb[8]]` is the list of the buffer's last 8 byte values. -/
theorem eval_jbBytes {σ : Type} (s : State σ) (env : SemEnv Value) (hc : HasListCons env.c) (ℓ : Nat)
    (hjb : nsLookup env.v (.short (ofString jbName)) = some (.loc true ℓ))
    (jb : List (BitVec 8)) (hlen : jb.length = 9) (hst : s.refs[ℓ]? = some (.w8array jb)) :
    evaluate s env [jbBytes] = (s, .val [natListV (byteNats (jb.drop 1))]) := by
  match jb, hlen with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8], _ =>
    have e : ∀ i (hi : i < 9), evaluate s env [jbByte i] =
        (s, .val [.litv (.intLit ([b0, b1, b2, b3, b4, b5, b6, b7, b8][i]'(by simpa using hi)).toNat)]) :=
      fun i hi => eval_byte env jbName ℓ hjb s _ i (by simpa using hi) hst
    unfold jbBytes
    rw [eval_consE s env hc _ _ _ _ (e 1 (by omega)) <|
        eval_consE s env hc _ _ _ _ (e 2 (by omega)) <|
        eval_consE s env hc _ _ _ _ (e 3 (by omega)) <|
        eval_consE s env hc _ _ _ _ (e 4 (by omega)) <|
        eval_consE s env hc _ _ _ _ (e 5 (by omega)) <|
        eval_consE s env hc _ _ _ _ (e 6 (by omega)) <|
        eval_consE s env hc _ _ _ _ (e 7 (by omega)) <|
        eval_consE s env hc _ _ _ _ (e 8 (by omega)) (eval_nilE s env hc)]
    simp [byteNats, natListV]

theorem eval_intEq {σ : Type} (s : State σ) (env : SemEnv Value) (x : String) (m n : Nat)
    (hx : nsLookup env.v (.short (ofString x)) = some (.litv (.intLit m))) :
    evaluate s env [intEq (var x) n] = (s, .val [boolValue (decide (m = n))]) := by
  simp +decide [intEq, evaluate, fixClock, getOpClass, headValue, Flapjack.holHd, doApp,
    doAppNumericCore, doAppBasic, var, hx, doEq, litSameType, listResult, Int.natCast_inj]

/-! ## `Runs` for FFI calls -/

theorem Runs.ffi_ret {σ : Type} (env : SemEnv Value) (s : State σ) (name bufN : String) (ce : Exp)
    (conf : MlString) (ℓ : Nat) (bytes out : List (BitVec 8)) (st' : σ)
    (hce : ∀ ck, evaluate { s with clock := ck } env [ce] = ({ s with clock := ck }, .val [.litv (.strLit conf)]))
    (hbuf : nsLookup env.v (.short (ofString bufN)) = some (.loc true ℓ))
    (hst : s.refs[ℓ]? = some (.w8array bytes))
    (hne : ofString name ≠ MlString.implode [])
    (ho : s.ffi.oracle (.extCall (ofString name)) s.ffi.ffiState conf.explode bytes = .ret st' out)
    (hlen : out.length = bytes.length) :
    Runs s env [.app (.ffi (ofString name)) [ce, var bufN]]
      { s with
          refs := s.refs.set ℓ (.w8array out)
          ffi := { s.ffi with
            ffiState := st'
            ioEvents := s.ffi.ioEvents ++ [ffiEvent name conf.explode bytes out] } }
      (.val [.conv none []]) :=
  ⟨0, 0, eval_ffi_ret env { s with clock := 0 } name bufN ce conf ℓ bytes out st' (hce 0) hbuf hst hne ho hlen⟩

theorem Runs.ffi_final {σ : Type} (env : SemEnv Value) (s : State σ) (name bufN : String) (ce : Exp)
    (conf : MlString) (ℓ : Nat) (bytes : List (BitVec 8)) (oc : HolFfiOutcome)
    (hce : ∀ ck, evaluate { s with clock := ck } env [ce] = ({ s with clock := ck }, .val [.litv (.strLit conf)]))
    (hbuf : nsLookup env.v (.short (ofString bufN)) = some (.loc true ℓ))
    (hst : s.refs[ℓ]? = some (.w8array bytes))
    (hne : ofString name ≠ MlString.implode [])
    (ho : s.ffi.oracle (.extCall (ofString name)) s.ffi.ffiState conf.explode bytes = .final oc) :
    Runs s env [.app (.ffi (ofString name)) [ce, var bufN]] s
      (.err (.abort (.ffiError (finalEvent name conf.explode bytes oc)))) :=
  ⟨0, 0, eval_ffi_final env { s with clock := 0 } name bufN ce conf ℓ bytes oc (hce 0) hbuf hst hne ho⟩

theorem Runs.let_abort {σ : Type} {s s₁ : State σ} {env : SemEnv Value} {n : Option VarN}
    {e₁ e₂ : Exp} {a : Abort} (h₁ : Runs s env [e₁] s₁ (.err (.abort a))) :
    Runs s env [.let_ n e₁ e₂] s₁ (.err (.abort a)) := by
  obtain ⟨a₁, a₂, ha⟩ := h₁
  exact ⟨a₁, a₂, evaluate_let_err ha⟩

/-- The result of a process that ended: normally, or by an FFI call ending the run. -/
def Ended (r : Result (List Value) Value) : Prop :=
  r = .val [.conv none []] ∨ ∃ ev, r = .err (.abort (.ffiError ev))

theorem Ended.not_timeout {r : Result (List Value) Value} (h : Ended r) :
    r ≠ .err (.abort .timeoutError) := by
  rcases h with rfl | ⟨ev, rfl⟩ <;> simp

/-! ## The loop -/

def workFuns (jobCodeName : String) : List (VarN × VarN × Exp) :=
  [(ofString workName, ofString "u", workBody jobCodeName)]

def workClosure (E : SemEnv Value) (jobCodeName : String) : Value :=
  .recclosure E (workFuns jobCodeName) (ofString workName)

theorem parOracle_ne (a b : String) (h : ofString a ≠ ofString b) : ofString a ≠ ofString b := h

section
variable {INVp : RefInv Phase1} (jobCodeName : String) (P : Phase1) (Ew : SemEnv Value) (ℓj : Nat)
  (pv jv : Value)

/-- What the loop needs of its closure environment. -/
structure WorkEnv : Prop where
  jb : nsLookup Ew.v (.short (ofString jbName)) = some (.loc true ℓj)
  p : nsLookup Ew.v (.short (ofString pName)) = some pv
  jc : nsLookup Ew.v (.short (ofString jobCodeName)) = some jv
  pinv : INVp P pv
  jinv : Arrow INVp (Arrow (LIST NAT) NAT) jobCode jv
  cons : HasListCons Ew.c
  n_u : ofString jobCodeName ≠ ofString "u"
  n_w : ofString jobCodeName ≠ ofString workName

end

/-! ## The oracle's answers to the worker's calls -/

theorem parOracle_claim (st : ParIO) (conf jb c : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (hjb : jb.length = 9) (hcl : st.claims = c :: rest) (hc : c.length = 8) :
    parOracle (.extCall (ofString "claim")) st conf jb = .ret { st with claims := rest } (jb.take 1 ++ c) := by
  simp +decide [parOracle, hjb, hcl, hc]

theorem parOracle_claim_none (st : ParIO) (conf jb : List (BitVec 8)) (hjb : jb.length = 9)
    (hcl : st.claims = []) :
    parOracle (.extCall (ofString "claim")) st conf jb = .final .failed := by
  simp +decide [parOracle, hjb, hcl]

theorem parOracle_claim_bad (st : ParIO) (conf jb c : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (hjb : jb.length = 9) (hcl : st.claims = c :: rest) (hc : c.length ≠ 8) :
    parOracle (.extCall (ofString "claim")) st conf jb = .final .failed := by
  simp +decide [parOracle, hjb, hcl, hc]

theorem parOracle_report (st : ParIO) (conf jb : List (BitVec 8)) (hjb : jb.length = 9) :
    parOracle (.extCall (ofString "report")) st conf jb = .ret st jb := by
  simp +decide [parOracle, hjb]

theorem ne_claim : ofString "claim" ≠ MlString.implode [] := by decide
theorem ne_report : ofString "report" ≠ MlString.implode [] := by decide

/-! ## The loop's environment -/

section
variable {INVp : RefInv Phase1} {jobCodeName : String} {P : Phase1} {Ew : SemEnv Value} {ℓj : Nat}
  {pv jv : Value}

def workBodyEnv (Ew : SemEnv Value) (jobCodeName : String) (uv : Value) : SemEnv Value :=
  recBodyEnv Ew (workFuns jobCodeName) (ofString "u") uv

theorem WorkEnv.lk_jb (h : WorkEnv (INVp := INVp) jobCodeName P Ew ℓj pv jv) (uv : Value) :
    nsLookup (workBodyEnv Ew jobCodeName uv).v (.short (ofString jbName)) = some (.loc true ℓj) := by
  have h1 : ofString jbName ≠ ofString "u" := by decide
  have h2 : ofString jbName ≠ ofString workName := by decide
  simp [workBodyEnv, recBodyEnv, workFuns, buildRecEnv, nsLookup_nsBind_short, h1, h2, h.jb]

theorem WorkEnv.lk_p (h : WorkEnv (INVp := INVp) jobCodeName P Ew ℓj pv jv) (uv : Value) :
    nsLookup (workBodyEnv Ew jobCodeName uv).v (.short (ofString pName)) = some pv := by
  have h1 : ofString pName ≠ ofString "u" := by decide
  have h2 : ofString pName ≠ ofString workName := by decide
  simp [workBodyEnv, recBodyEnv, workFuns, buildRecEnv, nsLookup_nsBind_short, h1, h2, h.p]

theorem WorkEnv.lk_jc (h : WorkEnv (INVp := INVp) jobCodeName P Ew ℓj pv jv) (uv : Value) :
    nsLookup (workBodyEnv Ew jobCodeName uv).v (.short (ofString jobCodeName)) = some jv := by
  simp [workBodyEnv, recBodyEnv, workFuns, buildRecEnv, nsLookup_nsBind_short, h.n_u, h.n_w, h.jc]

theorem lk_u (uv : Value) :
    nsLookup (workBodyEnv Ew jobCodeName uv).v (.short (ofString "u")) = some uv := by
  simp [workBodyEnv, recBodyEnv, nsLookup_nsBind_short]

theorem lk_work (uv : Value) :
    nsLookup (workBodyEnv Ew jobCodeName uv).v (.short (ofString workName)) =
      some (workClosure Ew jobCodeName) := by
  have h1 : ofString workName ≠ ofString "u" := by decide
  simp [workBodyEnv, recBodyEnv, workFuns, buildRecEnv, nsLookup_nsBind_short, h1, workClosure]

/-- Binding `c` keeps every other name. -/
theorem lk_bind_c (E : SemEnv Value) (cv : Value) (n : String) (hn : ofString n ≠ ofString "c") :
    nsLookup ({ E with v := nsOptBind (some (ofString "c")) cv E.v } : SemEnv Value).v (.short (ofString n)) =
      nsLookup E.v (.short (ofString n)) := by
  simp [nsOptBind, nsLookup_nsBind_short, hn]

theorem lk_c (E : SemEnv Value) (cv : Value) :
    nsLookup ({ E with v := nsOptBind (some (ofString "c")) cv E.v } : SemEnv Value).v (.short (ofString "c")) =
      some cv := by
  simp [nsOptBind, nsLookup_nsBind_short]

theorem refs_append_get {refs : Store Value} {ℓ : Nat} {x : StoreValue Value} (h : refs[ℓ]? = some x)
    (more : Store Value) : (refs ++ more)[ℓ]? = some x := by
  have hlt : ℓ < refs.length := by
    rcases Nat.lt_or_ge ℓ refs.length with h' | h'
    · exact h'
    · simp [List.getElem?_eq_none h'] at h
  rw [List.getElem?_append_left hlt, h]

theorem codeConf_three : codeConf 3 = (ofString "3").explode := rfl

/-- **The worker loop.** -/
theorem work_spec (h : WorkEnv (INVp := INVp) jobCodeName P Ew ℓj pv jv) (uv : Value) :
    ∀ (cl : List (List (BitVec 8))) (s : State ParIO) (jb : List (BitVec 8)), jb.length = 9 →
      s.refs[ℓj]? = some (.w8array jb) → s.ffi.oracle = parOracle → s.ffi.ffiState.claims = cl →
    ∃ s' r evs, Runs s (workBodyEnv Ew jobCodeName uv) [workBody jobCodeName] s' r ∧ Ended r ∧
      s'.ffi.ioEvents = s.ffi.ioEvents ++ evs ∧ s'.ffi.oracle = parOracle ∧
      ∀ e ∈ evs, IsCall "claim" e ∨ (IsCall "report" e ∧ ReportOk P e) := by
  intro cl
  induction cl with
  | nil =>
    intro s jb hjb hst hor hcl
    refine ⟨s, _, [], Runs.let_abort (Runs.ffi_final _ s "claim" jbName _ _ ℓj jb .failed
      (fun ck => eval_strLit _ _ "") (h.lk_jb uv) hst ne_claim ?_), .inr ⟨_, rfl⟩, by simp, hor, by simp⟩
    rw [hor]; exact parOracle_claim_none _ _ _ hjb hcl
  | cons c rest ih =>
    intro s jb hjb hst hor hcl
    by_cases hc : c.length = 8
    swap
    · refine ⟨s, _, [], Runs.let_abort (Runs.ffi_final _ s "claim" jbName _ _ ℓj jb .failed
        (fun ck => eval_strLit _ _ "") (h.lk_jb uv) hst ne_claim ?_), .inr ⟨_, rfl⟩, by simp, hor, by simp⟩
      rw [hor]; exact parOracle_claim_bad _ _ _ _ _ hjb hcl hc
    -- the claim
    let E := workBodyEnv Ew jobCodeName uv
    let jb' := jb.take 1 ++ c
    have hjb' : jb'.length = 9 := by simp [jb', hjb, hc]
    have hlt : ℓj < s.refs.length := by
      rcases Nat.lt_or_ge ℓj s.refs.length with h' | h'
      · exact h'
      · simp [List.getElem?_eq_none h'] at hst
    let evC := ffiEvent "claim" (ofString "").explode jb jb'
    let s₁ : State ParIO := { s with
      refs := s.refs.set ℓj (.w8array jb')
      ffi := { s.ffi with
        ffiState := { s.ffi.ffiState with claims := rest }
        ioEvents := s.ffi.ioEvents ++ [evC] } }
    have hclaim : Runs s E [ffiCall "claim" "" jbName] s₁ (.val [.conv none []]) :=
      Runs.ffi_ret _ s "claim" jbName _ _ ℓj jb jb' _ (fun ck => eval_strLit _ _ "") (h.lk_jb uv) hst
        ne_claim (by rw [hor]; exact parOracle_claim _ _ _ _ _ hjb hcl hc) (by rw [hjb', hjb])
    have hst₁ : s₁.refs[ℓj]? = some (.w8array jb') := List.getElem?_set_self hlt
    -- the job's code
    have hdrop : jb'.drop 1 = c := by
      have : (jb.take 1).length = 1 := by simp; omega
      simp [jb', List.drop_append, this]
    have hbytes : evaluate s₁ E [jbBytes] = (s₁, .val [natListV (byteNats c)]) := by
      rw [← hdrop]; exact eval_jbBytes s₁ E h.cons ℓj (h.lk_jb uv) jb' hjb' hst₁
    obtain ⟨fv, rf, hfRun, hf⟩ := Runs.app_returns
      (Runs.cons (Runs.var s₁ E pName pv (h.lk_p uv)) (Runs.var s₁ E jobCodeName jv (h.lk_jc uv)))
      (h.jinv P pv h.pinv)
    let s₂ : State ParIO := { s₁ with refs := s₁.refs ++ rf }
    obtain ⟨cv, rc, hcRun, hcv⟩ := Runs.app_returns
      (Runs.cons ⟨0, 0, by
        rw [← hdrop]; exact eval_jbBytes { s₁ with clock := 0 } E h.cons ℓj (h.lk_jb uv) jb' hjb' hst₁⟩ hfRun) (hf _ _ (LIST_natListV (byteNats c)))
    let s₃ : State ParIO := { s₂ with refs := s₂.refs ++ rc }
    have hcv' : cv = .litv (.intLit (jobCode P (byteNats c))) := hcv
    have hst₃ : s₃.refs[ℓj]? = some (.w8array jb') := refs_append_get (refs_append_get hst₁ rf) rc
    let k := jobCode P (byteNats c)
    let Ec : SemEnv Value := { E with v := nsOptBind (some (ofString "c")) cv E.v }
    have hEc_jb : nsLookup Ec.v (.short (ofString jbName)) = some (.loc true ℓj) := by
      rw [lk_bind_c _ _ _ (by decide)]; exact h.lk_jb uv
    have hEc_c : nsLookup Ec.v (.short (ofString "c")) = some (.litv (.intLit k)) := by
      rw [lk_c, hcv']
    -- the report
    let evR := ffiEvent "report" (codeConf k) jb' jb'
    have hR : ReportOk P evR := by
      unfold ReportOk reportIndex evR ffiEvent
      simp only [List.map_fst_zip (Nat.le_refl _), hdrop]
      rfl
    have hor₃ : s₃.ffi.oracle = parOracle := hor
    let s₄ : State ParIO := { s₃ with
      refs := s₃.refs.set ℓj (.w8array jb')
      ffi := { s₃.ffi with ioEvents := s₃.ffi.ioEvents ++ [evR] } }
    have hrep : ∀ ce, (∀ ck, evaluate { s₃ with clock := ck } Ec [ce] =
        ({ s₃ with clock := ck }, .val [.litv (.strLit (ofString (if k = 3 then "3" else if k = 1 then "1" else "2")))])) →
        Runs s₃ Ec [.app (.ffi (ofString "report")) [ce, var jbName]] s₄ (.val [.conv none []]) := by
      intro ce hce
      have := Runs.ffi_ret Ec s₃ "report" jbName ce _ ℓj jb' jb' s₃.ffi.ffiState hce hEc_jb hst₃ ne_report
        (by rw [hor₃]; exact parOracle_report _ _ _ hjb') rfl
      simpa [s₄, evR, codeConf] using this
    have hevs₄ : s₄.ffi.ioEvents = s.ffi.ioEvents ++ [evC, evR] := by simp [s₄, s₃, s₂, s₁]
    have hcalls : ∀ e ∈ [evC, evR], IsCall "claim" e ∨ (IsCall "report" e ∧ ReportOk P e) := by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact .inl rfl
      · exact .inr ⟨rfl, hR⟩
    have hif3 : ∀ ck, evaluate { s₃ with clock := ck } Ec [intEq (var "c") 3] =
        ({ s₃ with clock := ck }, .val [boolValue (decide (k = 3))]) :=
      fun ck => eval_intEq _ Ec "c" k 3 hEc_c
    have hthen : Runs s₃ Ec [.if_ (intEq (var "c") 3) (ffiCall "report" "3" jbName)
          (.let_ none (.app (.ffi (ofString "report")) [.if_ (intEq (var "c") 1) (strE "1") (strE "2"), var jbName])
            (.app .opapp [var workName, var "u"]))] s₄ (.val [.conv none []]) ∨ k ≠ 3 := by
      by_cases hk3 : k = 3
      · refine .inl (Runs.if_ ⟨0, 0, hif3 0⟩ ?_ (by simp))
        simp only [hk3, decide_true, ite_true]
        exact hrep _ fun ck => by simp only [hk3, ite_true]; exact eval_strLit _ _ "3"
      · exact .inr hk3
    have hmain : ∀ {s' : State ParIO} {r : Result (List Value) Value},
        Runs s₃ Ec [.if_ (intEq (var "c") 3) (ffiCall "report" "3" jbName)
          (.let_ none (.app (.ffi (ofString "report")) [.if_ (intEq (var "c") 1) (strE "1") (strE "2"), var jbName])
            (.app .opapp [var workName, var "u"]))] s' r → Ended r →
        Runs s E [workBody jobCodeName] s' r := by
      intro s' r hr he
      exact Runs.let_ hclaim (Runs.let_ hcRun hr he.not_timeout) he.not_timeout
    rcases hthen with h3 | hk3
    · exact ⟨s₄, _, [evC, evR], hmain h3 (.inl rfl), .inl rfl, hevs₄, hor, hcalls⟩
    · -- a job: report its code, then loop
      have hrep' := hrep (.if_ (intEq (var "c") 1) (strE "1") (strE "2")) fun ck => by
        rw [evaluate_if_val (eval_intEq _ Ec "c" k 1 hEc_c)]
        by_cases hk1 : k = 1 <;> simp [hk3, hk1, strE, evaluate]
      have hst₄ : s₄.refs[ℓj]? = some (.w8array jb') := by
        have hlt₃ : ℓj < s₃.refs.length := by
          rcases Nat.lt_or_ge ℓj s₃.refs.length with h' | h'
          · exact h'
          · simp [List.getElem?_eq_none h'] at hst₃
        exact List.getElem?_set_self hlt₃
      obtain ⟨s', r, evs, hrun, hend, hevs, hor', hall⟩ :=
        ih s₄ jb' hjb' hst₄ hor (by simp [s₄, s₃, s₂, s₁])
      have hEc_u : nsLookup Ec.v (.short (ofString "u")) = some uv := by
        rw [lk_bind_c _ _ _ (by decide)]; exact lk_u uv
      have hEc_w : nsLookup Ec.v (.short (ofString workName)) = some (workClosure Ew jobCodeName) := by
        rw [lk_bind_c _ _ _ (by decide)]; exact lk_work uv
      have happ : doOpApp [workClosure Ew jobCodeName, uv] =
          some (workBodyEnv Ew jobCodeName uv, workBody jobCodeName) := by
        simp [doOpApp, workClosure, workFuns, findRecFun, recBodyEnv, workBodyEnv]
      have hloop : Runs s₄ Ec [.app .opapp [var workName, var "u"]] s' r :=
        Runs.app_opapp_any (Runs.cons (Runs.var s₄ Ec "u" uv hEc_u) (Runs.var s₄ Ec workName _ hEc_w))
          happ hrun hend.not_timeout
      have hif : Runs s₃ Ec [.if_ (intEq (var "c") 3) (ffiCall "report" "3" jbName)
          (.let_ none (.app (.ffi (ofString "report")) [.if_ (intEq (var "c") 1) (strE "1") (strE "2"), var jbName])
            (.app .opapp [var workName, var "u"]))] s' r := by
        refine Runs.if_ ⟨0, 0, hif3 0⟩ ?_ hend.not_timeout
        simp only [show decide (k = 3) = false by simpa using hk3, Bool.false_eq_true, ite_false]
        exact Runs.let_ hrep' hloop hend.not_timeout
      refine ⟨s', r, [evC, evR] ++ evs, hmain hif hend, hend, by rw [hevs, hevs₄]; simp, hor', ?_⟩
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hcalls e he
      · exact hall e he
end

end ConPastel.Par
