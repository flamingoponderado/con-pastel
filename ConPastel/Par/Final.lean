import ConPastel.Par.Assemble

/-!
# The processes together: the parallel checker's verdict is con-leche's

`ParImplements prog`: in every run of the parallel harness that satisfies the harness assumptions
(`HarnessRun`), the parent writes con-leche's verdict.

**The harness assumptions** (not proved; `release/con_pastel_par_ffi.c` is meant to implement them):

* The parent is a run of `prog` on the input, with `spawn` answering "parent".
* If the parent spawned workers (its run contains a `spawn` call), the table `T` that `results`
  served it holds only the codes `1` and `2`, and
  - for each index `i < T.length`, some worker reported code `T[i]` for job `i`, and
  - some worker reported code `3` for job `T.length`,
  where a **worker** is a run of the same program on the same input, with `spawn` answering
  "worker", and "reported" means its run contains that `report` event.

`ParProcess` (the per-process theorem) gives what each run does. The rest is pure: a worker reports
only the code `runJob` computes for the index it reports, so the table is the jobs' codes, the end
marker sits at the number of jobs, and `verdictCode_table` gives con-leche's verdict.
-/

namespace ConPastel.Par
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticsHOL
open Flapjack.Basis.Pure.MlString ConPastel.Main

/-- The input bytes as the FFI model holds them. -/
def inputBits (input : ByteArray) : List (BitVec 8) := input.toList.map (·.toBitVec)

/-- A run of `prog` on the script `io` whose io-events are `events`. -/
def RunOf (prog : List Dec) (io : ParIO) (events : List HolIoEvent) : Prop :=
  ∃ st env, PrimTypesHOL.primSemEnv (initParFfi io) = some (st, env) ∧
    ∃ outcome, semanticsProg st env prog (.terminate outcome events)

/-- A worker on `input` reported code `c` for job `i`. -/
def Reported (prog : List Dec) (input : ByteArray) (i c : Nat) : Prop :=
  ∃ io events, io.input = inputBits input ∧ io.worker = true ∧ RunOf prog io events ∧
    ∃ e ∈ events, IsCall "report" e ∧ reportIndex e = i ∧ e.configuration = codeConf c

/-- **The harness assumptions**, for a parent run with script `io` and events `events`. -/
structure HarnessRun (prog : List Dec) (input : ByteArray) (io : ParIO) (events : List HolIoEvent) :
    Prop where
  sameInput : io.input = inputBits input
  parent : io.worker = false
  run : RunOf prog io events
  codes : (∃ e ∈ events, IsCall "spawn" e) →
    ∀ i (hi : i < io.table.length), (io.table[i].toNat = 1 ∨ io.table[i].toNat = 2) ∧
      Reported prog input i io.table[i].toNat
  last : (∃ e ∈ events, IsCall "spawn" e) → Reported prog input io.table.length 3

/-- **The parallel checker's statement**: under the harness assumptions, the parent writes
con-leche's verdict. -/
def ParImplements (prog : List Dec) : Prop :=
  ∀ (input : ByteArray) (io : ParIO) (events : List HolIoEvent), HarnessRun prog input io events →
    writtenBytes events = verdictBytes (conLecheAccepts input)

/-! ## Proofs -/

theorem events_of_run {prog : List Dec} (hp : ParProcess prog) {io : ParIO} {events : List HolIoEvent}
    (h : RunOf prog io events) : ProcOk io events := by
  obtain ⟨st, env, he, outcome, hb⟩ := h
  obtain ⟨st', env', he', outcome', events', hb', hok, huniq⟩ := hp io
  rw [he] at he'
  cases he'
  have := huniq _ hb
  cases this
  exact hok

theorem runJob_pos (P : Phase1) (k : Nat) : runJob P k = 1 ∨ runJob P k = 2 ∨ runJob P k = 3 := by
  unfold runJob; split
  · split <;> simp
  · simp

theorem runJob_three (P : Phase1) (k : Nat) : runJob P k = 3 ↔ P.ds.size ≤ k := by
  unfold runJob
  split
  · rename_i d hd
    have : k < P.ds.size := by
      rcases Nat.lt_or_ge k P.ds.size with h | h
      · exact h
      · simp [Array.getElem?_eq_none h] at hd
    split <;> simp <;> omega
  · rename_i hd
    have : P.ds.size ≤ k := by
      rcases Nat.lt_or_ge k P.ds.size with h | h
      · simp [Array.getElem?_eq_getElem h] at hd
      · exact h
    simp [this]

theorem codeConf_inj {a b : Nat} (ha : a = 1 ∨ a = 2 ∨ a = 3) (hb : b = 1 ∨ b = 2 ∨ b = 3)
    (h : codeConf a = codeConf b) : a = b := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> first | rfl | (revert h; decide)

/-- A worker's report is the job's code. -/
theorem reported_code {prog : List Dec} (hp : ParProcess prog) {input : ByteArray} {i c : Nat}
    (hc : c = 1 ∨ c = 2 ∨ c = 3) (h : Reported prog input i c) :
    runJob (phase1 (byteNats (inputBits input))) i = c := by
  obtain ⟨io, events, hin, -, hrun, e, he, hr, hi, hconf⟩ := h
  have hok := (events_of_run hp hrun).2.1 e he hr
  unfold ReportOk at hok
  rw [hi, phase1Of, hin] at hok
  exact codeConf_inj (runJob_pos _ _) hc (hok.symm.trans hconf)

theorem byteNats_inputBits (input : ByteArray) :
    byteNats (inputBits input) = input.toList.map UInt8.toNat := by
  simp [byteNats, inputBits, Function.comp_def]

/-- con-leche rejects an input whose first phase fails. -/
theorem not_accepts_of_phase1 (bs : List Nat) (h : (phase1 bs).ok = false) :
    conLecheAccepts (entryOf bs) = false := by
  unfold phase1 at h
  unfold conLecheAccepts
  rw [conLecheResult_eq]
  cases hr : records (entryOf bs) with
  | ok ds => rw [hr] at h; simp at h
  | error e => rfl

theorem byteArray_toList_loop' (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  induction h : bs.size - i generalizing i r with
  | zero =>
    unfold ByteArray.toList.loop
    have : ¬ i < bs.size := by omega
    simp only [this, ite_false]
    have : bs.data.toList.length ≤ i := by
      rw [Array.length_toList]; exact Nat.le_of_not_lt this
    simp [List.drop_eq_nil_of_le this]
  | succ n ih =>
    unfold ByteArray.toList.loop
    have hi : i < bs.size := by omega
    simp only [hi, ite_true]
    rw [ih (i+1) _ (by omega)]
    have hi2 : i < bs.data.size := hi
    have hi' : i < bs.data.toList.length := by rw [Array.length_toList]; exact hi2
    simp [ByteArray.get!, List.drop_eq_getElem_cons hi', getElem!_def, Array.getElem?_eq_getElem hi2]

theorem byteArray_toList' (bs : ByteArray) : bs.toList = bs.data.toList := by
  simp [ByteArray.toList, byteArray_toList_loop']

theorem entryOf_inputBits (input : ByteArray) : entryOf (byteNats (inputBits input)) = input := by
  rw [byteNats_inputBits]
  rcases input with ⟨⟨l⟩⟩
  simp [entryOf, byteArray_toList', Function.comp_def]

/-- **Composition**: one process's correctness and the harness assumptions give con-leche's
verdict. -/
theorem parImplements_of_process {prog : List Dec} (hp : ParProcess prog) : ParImplements prog := by
  intro input io events hh
  have hproc := events_of_run hp hh.run
  let bs := byteNats (inputBits input)
  let P := phase1 bs
  have hP : phase1Of io = P := by simp [phase1Of, hh.sameInput, P, bs]
  rw [hproc.1, expectedOut_eq, hP]
  unfold expectedOutP
  cases hok : P.ok
  · simp only [Bool.false_eq_true, ite_false]
    rw [← entryOf_inputBits input, not_accepts_of_phase1 bs hok]
  · simp only [ite_true, hh.parent, Bool.false_eq_true, ite_false]
    have hsp : ∃ e ∈ events, IsCall "spawn" e := hproc.2.2 (hP ▸ hok)
    let T := byteNats io.table
    -- the table is the jobs' codes, and its end is the number of jobs
    have hT : ∀ i (hi : i < T.length), T[i] = runJob P i := by
      intro i hi
      have hi' : i < io.table.length := by simpa [T, byteNats] using hi
      obtain ⟨hc, hrep⟩ := hh.codes hsp i hi'
      have := reported_code hp (by rcases hc with h | h <;> simp [h]) hrep
      simpa [T, P, bs, byteNats] using this.symm
    have hlast : runJob P T.length = 3 := by
      have := reported_code hp (by simp) (hh.last hsp)
      simpa [T, P, bs, byteNats] using this
    have hlen : T.length = P.ds.size := by
      have hge := (runJob_three P _).mp hlast
      rcases Nat.lt_or_ge P.ds.size T.length with hlt | hle
      · have h1 := hT P.ds.size hlt
        have h2 : runJob P P.ds.size = 3 := (runJob_three P _).mpr (Nat.le_refl _)
        have hi' : P.ds.size < io.table.length := by simpa [T, byteNats] using hlt
        obtain ⟨hc, -⟩ := hh.codes hsp _ hi'
        have : T[P.ds.size] = io.table[P.ds.size].toNat := by simp [T, byteNats]
        rw [this, h2] at h1
        rcases hc with hc | hc <;> omega
      · omega
    have hv := verdictCode_table bs hok T hlen hT
    simp only [T] at hv
    rw [hv, ← entryOf_inputBits input]
    cases conLecheAccepts (entryOf bs) <;> rfl

end ConPastel.Par
