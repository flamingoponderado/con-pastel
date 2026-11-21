import ConPastel.Par.Jobs
import ConPastel.Spec

/-!
# The phases of the jobs-based checker, as Lean functions

These are the functions the jobs-based CakeML programs call (they are translated as units):

* `phase1`: the sequential first phase, run once: parse, prepare the prelude, build the stream's
  index (`buildIndex`). Its result is what every worker inherits.
* `runJob p k`: job `k`'s code, `1` if it passes, `2` if it fails, `3` if there is no job `k`.
  `jobCode p bs` is the same for `k` given as 8 bytes, little-endian, as `claim` hands it out.
* `verdictCode p l`: the verdict on a table of job codes `l` in index order: `0` accept, `1`
  reject, `2` the table is not a table of `p`'s jobs.

`seqEntry` runs every job in order on one process; `seqEntry_eq` says it is con-leche's verdict.
`verdictCode_table` is the same for any table that holds every job's code, which is what the
parallel program's parent receives.
-/

namespace ConPastel.Par

open ConLeche ConLeche.Cached ConLeche.Frontend

/-- The first phase's result: whether the parse succeeded, the records and the stream's index. -/
structure Phase1 where
  ok : Bool
  ds : Array Declaration
  I : StreamIndex

/-- The input file from the values of its bytes. -/
def entryOf (bs : List Nat) : ByteArray := ⟨⟨bs.map UInt8.ofNat⟩⟩

/-- The records of the input, as con-leche's pipeline prepares them. -/
def records (input : ByteArray) : Except (CheckError × Nat) (Array Declaration) := do
  let pre ← builtinPreludeE
  let r ← parseChunks [input]
  pure (preparePrelude pre r.decls)

/-- **The first phase.** -/
def phase1 (bs : List Nat) : Phase1 :=
  match records (entryOf bs) with
  | .ok ds => ⟨true, ds, buildIndex ds⟩
  | .error _ => ⟨false, #[], {}⟩

/-- **Job `k`'s code**: `1` passes, `2` fails, `3` no such job. -/
def runJob (p : Phase1) (k : Nat) : Nat :=
  match p.ds[k]? with
  | some d =>
    match recordJob .verified natOpPinSets maxNatSizeDefault p.I k d with
    | .ok () => 1
    | .error _ => 2
  | none => 3

/-- A number from its bytes, little-endian. -/
def decodeLE : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * decodeLE bs

/-- Job code for an index given as bytes. -/
def jobCode (p : Phase1) (bs : List Nat) : Nat := runJob p (decodeLE bs)

/-- The first code of `l` that is not `1`, or `0` if there is none. -/
def firstNotOk : List Nat → Nat
  | [] => 0
  | c :: l => if c = 1 then firstNotOk l else c

/-- **The verdict on a table of job codes**: `0` accept, `1` reject, `2` not a table of `p`. -/
def verdictCode (p : Phase1) (l : List Nat) : Nat :=
  if l.length = p.ds.size then
    match firstNotOk l with
    | 0 => 0
    | 2 => 1
    | _ => 2
  else 2

/-- The codes of jobs `k, k+1, …`, `n` of them. -/
def jobCodes (p : Phase1) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => runJob p k :: jobCodes p n (k + 1)

/-- **Every job in order, on one process.** -/
def seqEntry (bs : List Nat) : Bool :=
  let p := phase1 bs
  if p.ok then verdictCode p (jobCodes p p.ds.size 0) == 0 else false

/-! ## Proofs -/

theorem conLecheResult_eq (input : ByteArray) :
    conLecheResult input =
      (records input).bind (checkDecls .verified natOpPinSets maxNatSizeDefault) := by
  unfold conLecheResult records
  simp only [bind, Except.bind, pure, Except.pure]
  cases builtinPreludeE <;> simp only
  cases parseChunks _ <;> rfl

theorem length_jobCodes (p : Phase1) : ∀ n k, (jobCodes p n k).length = n
  | 0, _ => rfl
  | n + 1, k => by simp [jobCodes, length_jobCodes p n (k + 1)]

theorem getElem_jobCodes (p : Phase1) : ∀ n k i (hi : i < (jobCodes p n k).length),
    (jobCodes p n k)[i] = runJob p (k + i)
  | 0, _, _, hi => by simp [jobCodes] at hi
  | n + 1, k, 0, _ => by simp [jobCodes]
  | n + 1, k, i + 1, hi => by
    simp only [jobCodes, List.getElem_cons_succ]
    rw [getElem_jobCodes p n (k + 1) i]
    congr 1; omega

theorem firstNotOk_zero {l : List Nat} (h : ∀ c ∈ l, c ≠ 0) :
    firstNotOk l = 0 ↔ ∀ c ∈ l, c = 1 := by
  induction l with
  | nil => simp [firstNotOk]
  | cons c l ih =>
    simp only [firstNotOk, List.mem_cons, forall_eq_or_imp]
    by_cases hc : c = 1
    · simp only [↓reduceIte, true_and, hc]
      exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    · simp only [hc, ↓reduceIte, false_and, iff_false]
      exact h c (List.mem_cons_self ..)

theorem firstNotOk_ne_one : ∀ l : List Nat, firstNotOk l ≠ 1
  | [] => by simp [firstNotOk]
  | c :: l => by
    unfold firstNotOk
    split
    · exact firstNotOk_ne_one l
    · assumption

/-- `firstNotOk` is the code at the first index that is not `1`. -/
theorem firstNotOk_spec : ∀ {l : List Nat}, firstNotOk l ≠ 0 →
    ∃ i, ∃ hi : i < l.length, (∀ j (hj : j < i), l[j]'(by omega) = 1) ∧ l[i] = firstNotOk l
  | [], h => by simp [firstNotOk] at h
  | c :: l, h => by
    by_cases hc : c = 1
    · simp only [firstNotOk, hc, ↓reduceIte] at h ⊢
      obtain ⟨i, hi, hpre, hi'⟩ := firstNotOk_spec h
      refine ⟨i + 1, by simp; omega, ?_, by simpa using hi'⟩
      intro j hj
      cases j with
      | zero => simp
      | succ j => simpa using hpre j (by omega)
    · simp only [firstNotOk, hc, ↓reduceIte]
      exact ⟨0, by simp, fun j hj => absurd hj (Nat.not_lt_zero _), rfl⟩

theorem runJob_ne_zero (p : Phase1) (k : Nat) : runJob p k ≠ 0 := by
  unfold runJob; split
  · split <;> simp
  · simp

/-- **A table that holds every job's code gives con-leche's verdict**: `0` if con-leche accepts the
input, `1` otherwise. -/
theorem verdictCode_table (bs : List Nat) (hok : (phase1 bs).ok = true) (l : List Nat)
    (hlen : l.length = (phase1 bs).ds.size)
    (hl : ∀ i (hi : i < l.length), l[i] = runJob (phase1 bs) i) :
    verdictCode (phase1 bs) l = if conLecheAccepts (entryOf bs) then 0 else 1 := by
  unfold phase1 at hok hlen hl ⊢
  unfold conLecheAccepts
  rw [conLecheResult_eq]
  cases hr : records (entryOf bs) with
  | error e => rw [hr] at hok; simp at hok
  | ok ds =>
    rw [hr] at hlen hl
    simp only at hlen hl ⊢
    have hjob : ∀ i (hi : i < ds.size), l[i]'(by omega) =
        match recordJob .verified natOpPinSets maxNatSizeDefault (buildIndex ds) i ds[i] with
        | .ok () => 1 | .error _ => 2 := by
      intro i hi
      rw [hl i (by omega)]
      simp only [runJob, Array.getElem?_eq_getElem hi]
    have hne : ∀ c ∈ l, c ≠ 0 := by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      rw [hl i hi]; exact runJob_ne_zero _ _
    unfold verdictCode
    have hb : (Except.ok ds : Except (CheckError × Nat) _).bind
        (checkDecls .verified natOpPinSets maxNatSizeDefault) =
        checkDecls .verified natOpPinSets maxNatSizeDefault ds := rfl
    simp only [hlen, ↓reduceIte, hb]
    by_cases h0 : firstNotOk l = 0
    · -- every job passes
      have hall := (firstNotOk_zero hne).mp h0
      have hjobs : ∀ k (hk : k < ds.size),
          recordJob .verified natOpPinSets maxNatSizeDefault (buildIndex ds) k ds[k] = .ok () := by
        intro k hk
        have h1 := hall _ (List.getElem_mem (l := l) (n := k) (by omega))
        rw [hjob k hk] at h1
        split at h1
        · assumption
        · simp at h1
      simp only [h0, checkDecls_of_jobs hjobs, ↓reduceIte]
    · obtain ⟨i, hi, hpre, hi'⟩ := firstNotOk_spec h0
      have hi2 : i < ds.size := by omega
      have hpre' : ∀ j (hj : j < ds.size), j < i →
          recordJob .verified natOpPinSets maxNatSizeDefault (buildIndex ds) j ds[j] = .ok () := by
        intro j hj hji
        have h1 := hpre j hji
        rw [hjob j hj] at h1
        split at h1
        · assumption
        · simp at h1
      have hcode := hjob i hi2
      split at hcode
      · -- the first entry that is not `1` is `1`: impossible
        rename_i hok'
        have : l[i] ≠ 1 := by rw [hi']; exact firstNotOk_ne_one l
        exact absurd hcode this
      · rename_i e he
        rw [hi'] at hcode
        simp only [checkDecls_error_of_jobs hi2 hpre' he, hcode]
        rfl

/-- **Every job in order, on one process, is con-leche's verdict.** -/
theorem seqEntry_eq (bs : List Nat) : seqEntry bs = conLecheAccepts (entryOf bs) := by
  unfold seqEntry
  by_cases hok : (phase1 bs).ok = true
  · simp only [hok, ↓reduceIte]
    rw [verdictCode_table bs hok _ (length_jobCodes _ _ _) (fun i hi => by
      rw [getElem_jobCodes]; simp)]
    split <;> simp_all
  · simp only [hok, Bool.false_eq_true, ↓reduceIte]
    unfold phase1 at hok
    unfold conLecheAccepts
    rw [conLecheResult_eq]
    cases hr : records (entryOf bs) with
    | ok ds => rw [hr] at hok; simp at hok
    | error e => rfl

end ConPastel.Par
