import ConPastel.Leche.Datatypes
import ConLeche.Verify.Frontend.Local

/-!
# Hash-consing the parsed expressions

CakeML has no pointer identity: every pointer test of con-leche runs as
"compare the cached data words, then CakeML `=`" (`ConPastel.Leche.Sharing`),
and `=` returns at once only on physically equal values. Two equal
expressions built separately (an export may bind the same term under two
indices, e.g. `tower_beqpair`) make every comparison walk the unshared tree:
exponential on DAGs.

The parse is where interning is cheap: each new node's children come from the
expression table, so they are already interned, and comparing the new node
with a stored candidate costs `O(1)` per child (equal children are the same
pointer). `parseChunksI` is `parseChunks` with an intern table threaded
through the serial parse: every expression-table entry is replaced by the
stored equal node, if there is one. The table only ever returns a node that
`exprEqB` found equal, so every function here returns the same value as its
original (`parseChunksI_eq`), with no invariant on the table.
-/

namespace ConPastel.Impl
open ConLeche ConLeche.Frontend

/-- The intern table: nodes by hash (the stored flag is unused). -/
abbrev ITab := ExprMemo Bool

/-- A stored node equal to `e`. -/
def findXL (e : Expr) : List (Expr × Bool) → Option Expr
  | [] => none
  | (x, _) :: t => if x.data == e.data && exprEqB x e then some x else findXL e t

def findX (e : Expr) : ITab → Nat → Option Expr
  | .leaf l, _ => findXL e l
  | .node a b, k => if k % 2 = 0 then findX e a (k / 2) else findX e b (k / 2)

theorem findXL_eq {e x : Expr} : ∀ {l : List (Expr × Bool)}, findXL e l = some x → x = e
  | [], h => by simp [findXL] at h
  | (y, _) :: t, h => by
    simp only [findXL] at h
    split at h
    · rename_i hy; cases h; exact exprEqB_sound (Bool.and_eq_true _ _ ▸ hy).2
    · exact findXL_eq h

theorem findX_eq {e x : Expr} : ∀ {t : ITab} {k : Nat}, findX e t k = some x → x = e
  | .leaf _, _, h => findXL_eq h
  | .node a b, k, h => by
    simp only [findX] at h
    split at h
    · exact findX_eq h
    · exact findX_eq h

/-- The interned `e`: a stored equal node, or `e` itself, then stored. -/
def internE (it : ITab) (e : Expr) : Expr × ITab :=
  match findX e it (ExprMemo.key e) with
  | some x => (x, it)
  | none => (e, ExprMemo.insert e true 16 it (ExprMemo.key e))

theorem internE_fst (it : ITab) (e : Expr) : (internE it e).1 = e := by
  unfold internE
  split
  · rename_i x h; exact findX_eq h
  · rfl

/-! ## The serial parse, with the table -/

def parseExprEntryDI (st : StateD) (it : ITab) (i : Nat) (r : ExprRec) : M (StateD × ITab) := do
  st.freshExpr i
  let e ← exprOf st.lk r
  let p := internE it e
  pure ({ st with exprs := st.exprs.insert i p.1 }, p.2)

theorem parseExprEntryDI_eq (st : StateD) (it : ITab) (i : Nat) (r : ExprRec) :
    (parseExprEntryDI st it i r).map Prod.fst = parseExprEntryD st i r := by
  simp only [parseExprEntryDI, parseExprEntryD, internE_fst]
  cases st.freshExpr i <;> simp [bind, Except.bind, Except.map, pure, Except.pure] <;>
    cases exprOf st.lk r <;> rfl

def applyRecordI (st : StateD) (it : ITab) (r : LineRec) : M ((StateD × ITab) ⊕ RecordVerdict) :=
  match r with
  | .expr i e => do pure (.inl (← parseExprEntryDI st it i e))
  | .name i n => do pure (.inl ((← parseNameEntryD st i n), it))
  | .level i l => do pure (.inl ((← parseLevelEntryD st i l), it))
  | .decl d => do
    match ← applyDeclD st d with
    | .inl s => pure (.inl (s, it))
    | .inr v => pure (.inr v)
  | .header => pure (.inl (st, it))
  | .blank => pure (.inl (st, it))

/-- Forget the table of a record's result. -/
def forgetR : (StateD × ITab) ⊕ RecordVerdict → StateD ⊕ RecordVerdict
  | .inl p => .inl p.1
  | .inr v => .inr v

theorem applyRecordI_eq (st : StateD) (it : ITab) (r : LineRec) :
    (applyRecordI st it r).map forgetR = applyRecord st r := by
  cases r with
  | expr i e =>
    have h := parseExprEntryDI_eq st it i e
    simp only [applyRecordI, applyRecord]
    revert h
    cases parseExprEntryDI st it i e <;> cases parseExprEntryD st i e <;>
      simp [bind, Except.bind, Except.map, pure, Except.pure, forgetR]
  | name i n =>
    simp only [applyRecordI, applyRecord]
    cases parseNameEntryD st i n <;> simp [bind, Except.bind, Except.map, pure, Except.pure, forgetR]
  | level i l =>
    simp only [applyRecordI, applyRecord]
    cases parseLevelEntryD st i l <;> simp [bind, Except.bind, Except.map, pure, Except.pure, forgetR]
  | decl d =>
    simp only [applyRecordI, applyRecord]
    cases applyDeclD st d with
    | error e => rfl
    | ok x => cases x <;> rfl
  | header => rfl
  | blank => rfl

def applyLineI (st : StateD) (it : ITab) (r : LineRec) (lineNo : Nat) :
    M ((StateD × ITab) ⊕ RecordVerdict) :=
  if r.placed (lineNo == 0) then applyRecordI st it r else throw r.misplaced

theorem applyLineI_eq (st : StateD) (it : ITab) (r : LineRec) (lineNo : Nat) :
    (applyLineI st it r lineNo).map forgetR = applyLine st r lineNo := by
  simp only [applyLineI, applyLine]
  split
  · exact applyRecordI_eq st it r
  · rfl

def feedChunkI (st : StateD) (it : ITab) (b : ByteArray) (i : USize) (lineNo : Nat) :
    Except (CheckError × Nat) (StateD × ITab × Nat × USize) :=
  if _h : i < b.usize then
    match scanLineSpec b i with
    | .err e =>
      if newlineFrom b i then
        .error (.internal (ScanErr.render ⟨e.offset - i.toNat, e.what⟩), lineNo + 1)
      else .ok (st, it, lineNo, i)
    | .ok r j =>
      if j == 0 then .ok (st, it, lineNo, i)
      else
        match applyLineI st it r lineNo with
        | .error msg => .error (.internal msg, lineNo + 1)
        | .ok (.inr v) => .error (v.toError, lineNo + 1)
        | .ok (.inl (st, it)) =>
          if _hj : i < j then feedChunkI st it b j (lineNo + 1)
          else .error (.internal "the line scanner made no progress", lineNo + 1)
  else .ok (st, it, lineNo, i)
termination_by b.size - i.toNat
decreasing_by
  exact Nat.sub_lt_sub_left (usizeInBounds b i _h) (USize.lt_iff_toNat_lt.mp _hj)

/-- Forget the table of a chunk's result. -/
def forgetF : StateD × ITab × Nat × USize → StateD × Nat × USize
  | (st, _, n, i) => (st, n, i)

theorem feedChunkI_eq (st : StateD) (it : ITab) (b : ByteArray) (i : USize) (lineNo : Nat) :
    (feedChunkI st it b i lineNo).map forgetF = feedChunk st b i lineNo := by
  rw [feedChunkI, feedChunk]
  by_cases hi : i < b.usize
  · rw [dif_pos hi, dif_pos hi]
    cases scanLineSpec b i with
    | err e => by_cases hn : newlineFrom b i <;> simp [hn, Except.map, forgetF]
    | ok r j =>
      simp only
      by_cases hj0 : (j == 0) = true
      · simp [hj0, Except.map, forgetF]
      · simp only [hj0]
        have h := applyLineI_eq st it r lineNo
        revert h
        cases applyLineI st it r lineNo with
        | error msg =>
          cases applyLine st r lineNo <;> simp [Except.map] <;> intro h <;> subst h <;> rfl
        | ok x =>
          cases applyLine st r lineNo with
          | error _ => simp [Except.map]
          | ok y =>
            simp only [Except.map, Except.ok.injEq]
            intro h; subst h
            cases x with
            | inr v => rfl
            | inl p =>
              simp only [forgetR]
              by_cases hj : i < j
              · simp only [hj, dite_true]; exact feedChunkI_eq p.1 p.2 b j (lineNo + 1)
              · simp [hj, Except.map]
  · rw [dif_neg hi, dif_neg hi]; rfl
termination_by b.size - i.toNat
decreasing_by
  exact Nat.sub_lt_sub_left (usizeInBounds b i hi) (USize.lt_iff_toNat_lt.mp hj)

def applyFinalLineI (st : StateD) (it : ITab) (b : ByteArray) (i : USize)
    (lineNo : Nat) : Except (CheckError × Nat) (StateD × ITab) :=
  match scanLineSpec b i with
  | .err e => .error (.internal (ScanErr.render ⟨e.offset - i.toNat, e.what⟩), lineNo + 1)
  | .ok r _ =>
    match applyLineI st it r lineNo with
    | .error msg => .error (.internal msg, lineNo + 1)
    | .ok (.inr v) => .error (v.toError, lineNo + 1)
    | .ok (.inl p) => .ok p

theorem applyFinalLineI_eq (st : StateD) (it : ITab) (b : ByteArray) (i : USize) (lineNo : Nat) :
    (applyFinalLineI st it b i lineNo).map Prod.fst = applyFinalLine st b i lineNo := by
  simp only [applyFinalLineI, applyFinalLine]
  cases scanLineSpec b i with
  | err e => rfl
  | ok r j =>
    simp only
    have h := applyLineI_eq st it r lineNo
    revert h
    cases applyLineI st it r lineNo with
    | error msg => cases applyLine st r lineNo <;> simp [Except.map] <;> intro h <;> subst h <;> rfl
    | ok x =>
      cases applyLine st r lineNo with
      | error _ => simp [Except.map]
      | ok y =>
        simp only [Except.map, Except.ok.injEq]
        intro h; subst h
        cases x <;> rfl

def chunkStepI (st : StateD) (it : ITab) (carry : ByteArray) (lineNo total : Nat) (buf0 : ByteArray) :
    Except (CheckError × Nat) (StateD × ITab × ByteArray × Nat × Nat) :=
  if total + buf0.size ≥ USize.size then .error sizeError
  else
    let buf := if carry.isEmpty then buf0 else carry ++ buf0
    match feedChunkI st it buf 0 lineNo with
    | .error e => .error e
    | .ok (st, it, lineNo, tail) =>
      .ok (st, it, buf.extract tail.toNat buf.size, lineNo, total + buf0.size)

def forgetS : StateD × ITab × ByteArray × Nat × Nat → StateD × ByteArray × Nat × Nat
  | (st, _, c, n, t) => (st, c, n, t)

theorem chunkStepI_eq (st : StateD) (it : ITab) (carry : ByteArray) (lineNo total : Nat)
    (buf0 : ByteArray) :
    (chunkStepI st it carry lineNo total buf0).map forgetS = chunkStep st carry lineNo total buf0 := by
  simp only [chunkStepI, chunkStep]
  split
  · rfl
  · have h := feedChunkI_eq st it (if carry.isEmpty then buf0 else carry ++ buf0) 0 lineNo
    revert h
    cases feedChunkI st it (if carry.isEmpty then buf0 else carry ++ buf0) 0 lineNo with
    | error e => cases feedChunk st (if carry.isEmpty then buf0 else carry ++ buf0) 0 lineNo <;>
        simp [Except.map] <;> intro h <;> subst h <;> rfl
    | ok x =>
      cases feedChunk st (if carry.isEmpty then buf0 else carry ++ buf0) 0 lineNo with
      | error _ => simp [Except.map]
      | ok y =>
        simp only [Except.map, Except.ok.injEq]
        intro h; subst h
        rfl

def chunkFinishI (st : StateD) (it : ITab) (carry : ByteArray) (lineNo : Nat) :
    Except (CheckError × Nat) ParseResultD :=
  if carry.isEmpty then .ok (.ofState st)
  else
    match applyFinalLineI st it carry 0 lineNo with
    | .error e => .error e
    | .ok p => .ok (.ofState p.1)

theorem chunkFinishI_eq (st : StateD) (it : ITab) (carry : ByteArray) (lineNo : Nat) :
    chunkFinishI st it carry lineNo = chunkFinish st carry lineNo := by
  simp only [chunkFinishI, chunkFinish]
  split
  · rfl
  · have h := applyFinalLineI_eq st it carry 0 lineNo
    revert h
    cases applyFinalLineI st it carry 0 lineNo <;> cases applyFinalLine st carry 0 lineNo <;>
      simp [Except.map] <;> intro h <;> subst h <;> rfl

/-! ### The line loop on the unread list

`scanLineSpec b i` reads the line at `i` off `tailAt b i`, the array's bytes
from `i`: in the translation an array is a list, so that is a walk of the
whole input per line. `feedChunkL` scans each line on the previous line's
rest instead (the naive scanner's own continuation), and is proved equal to
`feedChunkI` through con-leche's position lemmas (`tailAt_posAt`). -/

theorem naiveLine_suffix (l : List UInt8) : (naiveLine l).rest <:+ l := by
  unfold naiveLine
  have hd := List.dropWhile_suffix (l := l) (p := isWs)
  split
  · rename_i rest h; rw [h] at hd; exact (List.suffix_cons _ _).trans hd
  · simp [NRes.rest]
  · rename_i l' h
    split
    · rename_i t r h2; simp only [NRes.rest]
      have := NRes.suffix_of_err h2 (naiveLineLoop_rest_suffix _ _ _ _)
      rw [h] at hd; exact this.trans ((List.suffix_cons _ _).trans hd)
    · rename_i r l2 h2
      have h3 : l2 <:+ l' := NRes.suffix_of_ok h2 (naiveLineLoop_rest_suffix _ _ _ _)
      have h4 : l2 <:+ l := h3.trans ((List.suffix_cons _ _).trans (h ▸ hd))
      have hd2 := List.dropWhile_suffix (l := l2) (p := isWs)
      split
      · rename_i rest h5; rw [h5] at hd2; exact ((List.suffix_cons _ _).trans hd2).trans h4
      · simp [NRes.rest]
      · simp only [NRes.rest]; exact hd2.trans h4
  · simp only [NRes.rest]; exact hd

theorem naiveLine_some_lt {l rest x : List UInt8} {r : LineRec}
    (h : naiveLine l = .ok (r, some x) rest) : rest.length < l.length := by
  unfold naiveLine at h
  have hd := (List.dropWhile_suffix (l := l) (p := isWs)).length_le
  split at h
  · rename_i rest' h1; cases h; rw [h1] at hd; simp at hd; omega
  · cases h
  · rename_i l' h1
    split at h
    · cases h
    · rename_i r' l2 h2
      have h3 := (NRes.suffix_of_ok h2 (naiveLineLoop_rest_suffix _ _ _ _)).length_le
      have hd2 := (List.dropWhile_suffix (l := l2) (p := isWs)).length_le
      split at h
      · rename_i rest' h5; cases h; rw [h5] at hd2; rw [h1] at hd; simp at hd hd2; omega
      · cases h
      · cases h
  · cases h

/-- `feedChunkI` on the unread input `tl` itself: each line's scan continues
on the previous one's rest, instead of re-reading the array from the line's
position (`tailAt`, a walk of the whole input per line in the translation,
where an array is a list). The position is only computed for an error. -/
def feedChunkL (st : StateD) (it : ITab) (b : ByteArray) (tl : List UInt8) (lineNo : Nat) :
    Except (CheckError × Nat) (StateD × ITab × Nat × List UInt8) :=
  match tl with
  | [] => .ok (st, it, lineNo, [])
  | c :: cs =>
    match naiveLine (c :: cs) with
    | .err t rest =>
      if newlineFrom b ((bytes b).length - (c :: cs).length).toUSize then
        .error (.internal (ScanErr.render ⟨(c :: cs).length - rest.length, t⟩), lineNo + 1)
      else .ok (st, it, lineNo, c :: cs)
    | .ok (_, none) _ => .ok (st, it, lineNo, c :: cs)
    | .ok (r, some _) rest =>
      match applyLineI st it r lineNo with
      | .error msg => .error (.internal msg, lineNo + 1)
      | .ok (.inr v) => .error (v.toError, lineNo + 1)
      | .ok (.inl (st, it)) =>
        if _h : rest.length < (c :: cs).length then feedChunkL st it b rest (lineNo + 1)
        else .error (.internal "the line scanner made no progress", lineNo + 1)
termination_by tl.length

/-- A chunk result's position, read as the unread input there. -/
def tailF (b : ByteArray) : StateD × ITab × Nat × USize → StateD × ITab × Nat × List UInt8
  | (st, it, n, j) => (st, it, n, tailAt b j)

theorem feedChunkL_eq (st : StateD) (it : ITab) (b : ByteArray) (i : USize) (lineNo : Nat)
    (hi : i.toNat ≤ (bytes b).length) :
    feedChunkL st it b (tailAt b i) lineNo = (feedChunkI st it b i lineNo).map (tailF b) := by
  rw [feedChunkI]
  by_cases hlt : i < b.usize
  · rw [dif_pos hlt]
    have hne : tailAt b i ≠ [] := by
      intro h; have := congrArg List.length h
      simp only [length_tailAt, List.length_nil] at this
      have := USize.lt_iff_toNat_lt.mp hlt; omega
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    have hsuf := naiveLine_suffix (tailAt b i)
    have hlt' : ∀ {r : LineRec} {x rest : List UInt8},
        naiveLine (tailAt b i) = .ok (r, some x) rest → rest.length < (tailAt b i).length :=
      fun h => naiveLine_some_lt h
    rw [hcs] at hsuf hlt' ⊢
    rw [feedChunkL]
    simp only [scanLineSpec, hcs]
    rcases hn : naiveLine (c :: cs) with ⟨⟨r, _ | x⟩, rest⟩ | ⟨t, rest⟩
    · simp [Except.map, tailF, hcs]
    · have hrs : rest <:+ tailAt b i := by rw [hcs]; rw [hn] at hsuf; exact hsuf
      have hl : rest.length < (c :: cs).length := hlt' hn
      have h1 := toNat_toUSize_posAt hi hrs
      have h2 := posAt_le hi hrs
      have htl := tailAt_posAt hi hrs
      rw [hcs] at h1 h2 htl
      have hj0 : (posAt i.toNat (c :: cs) rest).toUSize ≠ 0 := by
        intro h0; rw [h0] at h1; simp only [USize.toNat_zero, posAt] at h1; omega
      have hij : i < (posAt i.toNat (c :: cs) rest).toUSize := by
        rw [USize.lt_iff_toNat_lt, h1]; simp only [posAt]; omega
      have hj0' : USize.ofNat (posAt i.toNat (c :: cs) rest) ≠ 0 := hj0
      have hj0b : ((posAt i.toNat (c :: cs) rest).toUSize == 0) = false := by simpa using hj0
      have hij' : i < USize.ofNat (posAt i.toNat (c :: cs) rest) := hij
      rcases ha : applyLineI st it r lineNo with msg | ⟨⟨st', it'⟩ | v⟩
      · simp [Except.map, hj0', hj0b, ha]
      · simp only [ha, dif_pos hl, hij, hij', hj0', hj0b, if_true, if_false, dite_true, Bool.false_eq_true]
        have hle : (posAt i.toNat (c :: cs) rest).toUSize.toNat ≤ (bytes b).length := by
          rw [h1]; exact h2
        rw [← feedChunkL_eq st' it' b _ (lineNo + 1) hle, htl]
      · simp [Except.map, hj0', hj0b, ha]
    · have hpos : ((bytes b).length - (c :: cs).length).toUSize = i := by
        rw [← hcs, length_tailAt, length_bytes]
        have := USize.lt_iff_toNat_lt.mp hlt
        rw [show b.usize.toNat - (b.usize.toNat - i.toNat) = i.toNat by omega]
        exact USize.ofNat_toNat
      rw [hpos]
      by_cases hnl : newlineFrom b i = true
      · simp only [hnl, if_true, Except.map, posAt]
        congr 5; omega
      · simp [hnl, Except.map, tailF, hcs]
  · rw [dif_neg hlt, tailAt_of_not_lt hlt, feedChunkL]
    simp [Except.map, tailF, tailAt_of_not_lt hlt]
termination_by b.size - i.toNat
decreasing_by
  exact Nat.sub_lt_sub_left (usizeInBounds b i hlt) (USize.lt_iff_toNat_lt.mp hij)

theorem feedChunkI_le (st : StateD) (it : ITab) (b : ByteArray) (i : USize) (lineNo : Nat)
    (hi : i.toNat ≤ (bytes b).length) :
    ∀ x, feedChunkI st it b i lineNo = .ok x → x.2.2.2.toNat ≤ (bytes b).length := by
  intro x hx
  rw [feedChunkI] at hx
  by_cases hlt : i < b.usize
  · rw [dif_pos hlt] at hx
    simp only [scanLineSpec] at hx
    have hsuf := naiveLine_suffix (tailAt b i)
    rcases hn : naiveLine (tailAt b i) with ⟨⟨r, _ | y⟩, rest⟩ | ⟨t, rest⟩ <;> rw [hn] at hx
    · simp at hx; rw [← hx]; exact hi
    · have hrs : rest <:+ tailAt b i := by rw [hn] at hsuf; exact hsuf
      have h1 := toNat_toUSize_posAt hi hrs
      have h2 := posAt_le hi hrs
      simp only at hx
      split at hx
      · cases hx; exact hi
      · split at hx
        · cases hx
        · cases hx
        · by_cases hij : i < (posAt i.toNat (tailAt b i) rest).toUSize
          · rw [dif_pos hij] at hx
            have hle : (posAt i.toNat (tailAt b i) rest).toUSize.toNat ≤ (bytes b).length := by
              rw [h1]; exact h2
            exact feedChunkI_le _ _ b _ (lineNo + 1) hle x hx
          · rw [dif_neg hij] at hx; cases hx
    · simp only at hx; split at hx
      · cases hx
      · cases hx; exact hi
  · rw [dif_neg hlt] at hx; cases hx; exact hi
termination_by b.size - i.toNat
decreasing_by
  exact Nat.sub_lt_sub_left (usizeInBounds b i hlt) (USize.lt_iff_toNat_lt.mp hij)

/-! ### Lines cut at their newline -/

/-- The input up to its first newline, and the rest after it. -/
def splitNl : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | c :: l => if c == 10 then some ([], l) else (splitNl l).map fun (p, x) => (c :: p, x)

theorem splitNl_some : ∀ {l pre x : List UInt8}, splitNl l = some (pre, x) → l = pre ++ 10 :: x ∧ 10 ∉ pre
  | [], _, _, h => by simp [splitNl] at h
  | c :: l, pre, x, h => by
    simp only [splitNl] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [beq_iff_eq] at hc
      simp [hc]
    · rename_i hc
      rcases hs : splitNl l with _ | ⟨p, y⟩ <;> rw [hs] at h
      · simp at h
      · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := splitNl_some hs
        refine ⟨by simp [h1], ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨fun h => hc (by simp [← h]), h2⟩

/-- `feedChunkL`, scanning each line cut at its newline: the scanners'
progress guards measure the remaining input, so on the whole unread input
each costs a walk of it. A line is read inside its line (con-leche's
`naiveLine_local`), so the scan of the cut line is the scan of the input.
The recursion is on `fuel` (structural); out of fuel, `feedChunkL` takes
over, so the result is `feedChunkL`'s for every `fuel`. -/
def feedChunkC (fuel : Nat) (st : StateD) (it : ITab) (b : ByteArray) (tl : List UInt8) (lineNo : Nat) :
    Except (CheckError × Nat) (StateD × ITab × Nat × List UInt8) :=
  match fuel with
  | 0 => feedChunkL st it b tl lineNo
  | fuel + 1 =>
    match splitNl tl with
    | none => feedChunkL st it b tl lineNo
    | some (pre, x) =>
      match naiveLine (pre ++ [10]) with
      | .err t rest =>
        if newlineFrom b ((bytes b).length - tl.length).toUSize then
          .error (.internal (ScanErr.render ⟨(pre ++ [10]).length - rest.length, t⟩), lineNo + 1)
        else .ok (st, it, lineNo, tl)
      | .ok (_, none) _ => .ok (st, it, lineNo, tl)
      | .ok (r, some _) _ =>
        match applyLineI st it r lineNo with
        | .error msg => .error (.internal msg, lineNo + 1)
        | .ok (.inr v) => .error (v.toError, lineNo + 1)
        | .ok (.inl (st, it)) => feedChunkC fuel st it b x (lineNo + 1)

theorem feedChunkC_eq (fuel : Nat) (st : StateD) (it : ITab) (b : ByteArray) (tl : List UInt8)
    (lineNo : Nat) : feedChunkC fuel st it b tl lineNo = feedChunkL st it b tl lineNo := by
  induction fuel generalizing st it tl lineNo with
  | zero => rfl
  | succ fuel ih =>
  rw [feedChunkC]
  split
  · rfl
  · rename_i pre x h
    obtain ⟨rfl, hpre⟩ := splitNl_some h
    rcases naiveLine_local pre hpre with ⟨r, hr⟩ | ⟨t, r', _, hr⟩
    · have h0 := hr []
      rw [h0]
      obtain ⟨c, cs, hcs⟩ : ∃ c cs, pre ++ 10 :: x = c :: cs := by
        cases pre <;> simp
      have hx := hr x
      rw [hcs] at hx ⊢
      rw [feedChunkL, hx]
      simp only
      have hl : x.length < (c :: cs).length := by rw [← hcs]; simp; omega
      rcases ha : applyLineI st it r lineNo with msg | ⟨⟨st', it'⟩ | v⟩
      · rfl
      · simp only [hl, dite_true]
        exact ih st' it' x (lineNo + 1)
      · rfl
    · have h0 := hr []
      rw [h0]
      obtain ⟨c, cs, hcs⟩ : ∃ c cs, pre ++ 10 :: x = c :: cs := by
        cases pre <;> simp
      have hx := hr x
      rw [hcs] at hx ⊢
      rw [feedChunkL, hx]
      simp only
      have : (pre ++ [10]).length - (r' ++ [10]).length = (c :: cs).length - (r' ++ 10 :: x).length := by
        rw [← hcs]; simp; omega
      rw [this]

/-- `chunkStepI` with the list-carrying line loop. -/
def chunkStepL (st : StateD) (it : ITab) (carry : ByteArray) (lineNo total : Nat) (buf0 : ByteArray) :
    Except (CheckError × Nat) (StateD × ITab × ByteArray × Nat × Nat) :=
  if total + buf0.size ≥ USize.size then .error sizeError
  else
    let buf := if carry.isEmpty then buf0 else carry ++ buf0
    match feedChunkC buf.size st it buf (bytes buf) lineNo with
    | .error e => .error e
    | .ok (st, it, lineNo, tl) =>
      .ok (st, it, buf.extract ((bytes buf).length - tl.length) buf.size, lineNo, total + buf0.size)

theorem chunkStepL_eq (st : StateD) (it : ITab) (carry : ByteArray) (lineNo total : Nat)
    (buf0 : ByteArray) :
    chunkStepL st it carry lineNo total buf0 = chunkStepI st it carry lineNo total buf0 := by
  simp only [chunkStepL, chunkStepI]
  split
  · rfl
  · rw [feedChunkC_eq]
    generalize (if carry.isEmpty then buf0 else carry ++ buf0) = buf
    have h0 : (0 : USize).toNat ≤ (bytes buf).length := by simp
    have hb : bytes buf = tailAt buf 0 := by simp [tailAt]
    have hle := feedChunkI_le st it buf 0 lineNo h0
    rw [hb, feedChunkL_eq st it buf 0 lineNo h0]
    rcases hf : feedChunkI st it buf 0 lineNo with e | ⟨st', it', n, j⟩
    · rfl
    · have hj := hle _ hf
      simp only [Except.map, tailF, length_tailAt, ← hb]
      simp only [length_bytes] at hj
      rw [show (bytes buf).length - (buf.usize.toNat - j.toNat) = j.toNat by
        simp only [length_bytes]; omega]
def parseChunksGoI (st : StateD) (it : ITab) (carry : ByteArray) (lineNo total : Nat) :
    List ByteArray → Except (CheckError × Nat) ParseResultD
  | [] => chunkFinishI st it carry lineNo
  | c :: cs =>
    match chunkStepL st it carry lineNo total c with
    | .error e => .error e
    | .ok (st, it, carry, lineNo, total) => parseChunksGoI st it carry lineNo total cs

theorem parseChunksGoI_eq (st : StateD) (it : ITab) (carry : ByteArray) (lineNo total : Nat) :
    ∀ cs, parseChunksGoI st it carry lineNo total cs = parseChunks.go st carry lineNo total cs
  | [] => chunkFinishI_eq st it carry lineNo
  | c :: cs => by
    simp only [parseChunksGoI, parseChunks.go]
    have h := chunkStepI_eq st it carry lineNo total c
    rw [← chunkStepL_eq] at h
    revert h
    cases chunkStepL st it carry lineNo total c with
    | error e => cases chunkStep st carry lineNo total c <;> simp [Except.map] <;> intro h <;> subst h <;> rfl
    | ok x =>
      cases chunkStep st carry lineNo total c with
      | error _ => simp [Except.map]
      | ok y =>
        simp only [Except.map, Except.ok.injEq]
        intro h; subst h
        exact parseChunksGoI_eq _ _ _ _ _ cs

/-- `parseChunks`, interning every parsed expression. -/
def parseChunksI (chunks : List ByteArray) : Except (CheckError × Nat) ParseResultD :=
  parseChunksGoI .init (.leaf []) .empty 0 0 chunks

theorem parseChunks_eq_I (chunks : List ByteArray) : parseChunks chunks = parseChunksI chunks :=
  (parseChunksGoI_eq .init (.leaf []) .empty 0 0 chunks).symm

end ConPastel.Impl
