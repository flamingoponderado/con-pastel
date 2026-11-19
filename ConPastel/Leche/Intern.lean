import ConPastel.Leche.Datatypes

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

def parseChunksGoI (st : StateD) (it : ITab) (carry : ByteArray) (lineNo total : Nat) :
    List ByteArray → Except (CheckError × Nat) ParseResultD
  | [] => chunkFinishI st it carry lineNo
  | c :: cs =>
    match chunkStepI st it carry lineNo total c with
    | .error e => .error e
    | .ok (st, it, carry, lineNo, total) => parseChunksGoI st it carry lineNo total cs

theorem parseChunksGoI_eq (st : StateD) (it : ITab) (carry : ByteArray) (lineNo total : Nat) :
    ∀ cs, parseChunksGoI st it carry lineNo total cs = parseChunks.go st carry lineNo total cs
  | [] => chunkFinishI_eq st it carry lineNo
  | c :: cs => by
    simp only [parseChunksGoI, parseChunks.go]
    have h := chunkStepI_eq st it carry lineNo total c
    revert h
    cases chunkStepI st it carry lineNo total c with
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
