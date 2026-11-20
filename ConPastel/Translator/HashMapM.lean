import ConPastel.Translator.Table
import Batteries.Tactic.OpenPrivate

/-!
# Std's hash map operations, in place

`getM`, `insertM`, `sizeM` and `emptyM` are Std's `Raw₀.Const.get?`,
`Raw₀.insert`, `size` and `emptyWithCapacity`, written with the table
primitives (`ConPastel.Translator.Table`) step for step as Std writes them:
the same index (`mkIdx`), the same bucket operations, the same growth test,
and growth reinserting the entries in Std's order. Each is proved *equal* to
Std's operation on the raw map (`getM_eq`, `insertM_eq`, …), so the table
the store holds is always exactly the raw map of the Lean value.
-/

namespace ConPastel.Translator
open Std.DHashMap.Internal
open private Raw₀.expand.go numBucketsForCapacity from Std.Data.DHashMap.Internal.Defs
open private Nat.nextPowerOfTwo.go from Init.Data.Nat.Power2.Basic

section
variable {K V ε : Type} [BEq K] [Hashable K]

/-- Std's bucket index (`mkIdx`) in a table of `n` buckets. -/
def idxOf (n : Nat) (k : K) : Nat :=
  if h : 0 < n then (mkIdx n h (hash k)).1.toNat else 0

/-- `m[k]?`. -/
def getM (k : K) : StateT (TRaw K V) (Except ε) (Option V) := do
  let n ← tNB
  let bkt ← tGetB (idxOf n k)
  pure (bkt.get? k)

/-- `m.size`. -/
def sizeM : StateT (TRaw K V) (Except ε) Nat := tSize

/-- Put one entry at the head of its bucket (`reinsertAux`). -/
def reinsertOneM (k : K) (v : V) : StateT (TRaw K V) (Except ε) Unit := do
  let n ← tNB
  let i := idxOf n k
  let bkt ← tGetB i
  tSetB i (.cons k v bkt)

/-- Reinsert a bucket's entries, head first (`AssocList.foldl reinsertAux`). -/
def reinsertBktM : Bkt K V → StateT (TRaw K V) (Except ε) Unit
  | .nil => pure ()
  | .cons k v t => do reinsertOneM k v; reinsertBktM t

/-- Reinsert the buckets, in order. -/
def reinsertAllM : List (Bkt K V) → StateT (TRaw K V) (Except ε) Unit
  | [] => pure ()
  | b :: bs => do reinsertBktM b; reinsertAllM bs

/-- The buckets `i, …, n - 1`. -/
def readFromM (n : Nat) (i : Nat) : StateT (TRaw K V) (Except ε) (List (Bkt K V)) :=
  if i < n then do
    let b ← tGetB i
    let bs ← readFromM n (i + 1)
    pure (b :: bs)
  else pure []
termination_by n - i

/-- Double the buckets and reinsert every entry (`expand`). -/
def expandM : StateT (TRaw K V) (Except ε) Unit := do
  let n ← tNB
  let olds ← readFromM n 0
  tRealloc (n * 2)
  reinsertAllM olds

/-- Grow when the load factor passes 3/4 (`expandIfNecessary`). -/
def expandIfNecessaryM : StateT (TRaw K V) (Except ε) Unit := do
  let sz ← tSize
  let n ← tNB
  if sz * 4 / 3 ≤ n then pure () else expandM

/-- `m.insert k v`. -/
def insertM (k : K) (v : V) : StateT (TRaw K V) (Except ε) Unit := do
  let n ← tNB
  let i := idxOf n k
  let bkt ← tGetB i
  if bkt.contains k then tSetB i (bkt.replace k v)
  else do
    tSetB i (.cons k v bkt)
    let sz ← tSize
    tSetSize (sz + 1)
    expandIfNecessaryM

/-- `∅` (`emptyWithCapacity 8`): sixteen empty buckets, size `0`. -/
def emptyM : StateT (TRaw K V) (Except ε) Unit := do
  tRealloc 16
  tSetSize 0

end

/-! ## Equal to Std's operations -/

section
variable {K V ε : Type} [BEq K] [Hashable K]

omit [BEq K] in
theorem idxOf_eq {n : Nat} (h : 0 < n) (k : K) : idxOf n k = (mkIdx n h (hash k)).1.toNat := by
  simp [idxOf, h]

omit [BEq K] in
theorem getD_mkIdx (bs : Array (Bkt K V)) (h : 0 < bs.size) (k : K) :
    bs.getD (idxOf bs.size k) .nil = bs[(mkIdx bs.size h (hash k)).1.toNat]'(mkIdx bs.size h (hash k)).2 := by
  rw [idxOf_eq h]
  have := (mkIdx bs.size h (hash k)).2
  simp [Array.getD, this]

theorem getM_eq (m : Raw₀ K (fun _ => V)) (k : K) :
    (getM k : StateT (TRaw K V) (Except ε) (Option V)) m.1 = .ok (Raw₀.Const.get? m k, m.1) := by
  obtain ⟨⟨sz, bs⟩, h⟩ := m
  simp only [getM, tNB, tGetB, bind, StateT.bind, pure, StateT.pure, Except.bind]
  show Except.ok ((bs.getD (idxOf bs.size k) .nil).get? k, _) = _
  rw [getD_mkIdx bs h k]
  rfl

omit [BEq K] in
theorem setIB_mkIdx (bs : Array (Bkt K V)) (h : 0 < bs.size) (k : K) (x : Bkt K V) :
    bs.setIfInBounds (idxOf bs.size k) x = bs.uset (mkIdx bs.size h (hash k)).1 x (mkIdx bs.size h (hash k)).2 := by
  rw [idxOf_eq h]
  have := (mkIdx bs.size h (hash k)).2
  simp [Array.setIfInBounds, this, Array.uset]

omit [BEq K] in
/-- One reinsertion is `reinsertAux`. -/
theorem reinsertOneM_eq (raw : TRaw K V) (h : 0 < raw.buckets.size) (k : K) (v : V) :
    (reinsertOneM k v : StateT (TRaw K V) (Except ε) Unit) raw =
      .ok ((), { raw with buckets := (Raw₀.reinsertAux hash ⟨raw.buckets, h⟩ k v).1 }) := by
  obtain ⟨sz, bs⟩ := raw
  simp only [reinsertOneM, tNB, tGetB, tSetB, bind, StateT.bind, pure, StateT.pure, Except.bind]
  show Except.ok ((), ({ size := sz, buckets := bs.setIfInBounds (idxOf bs.size k) (.cons k v (bs.getD (idxOf bs.size k) .nil)) } : TRaw K V)) = _
  rw [getD_mkIdx bs h k, setIB_mkIdx bs h k]
  rfl

omit [BEq K] in
theorem reinsertAux_size (t : { d : Array (Bkt K V) // 0 < d.size }) (k : K) (v : V) :
    (Raw₀.reinsertAux hash t k v).1.size = t.1.size := by
  obtain ⟨d, hd⟩ := t
  simp [Raw₀.reinsertAux]

omit [BEq K] in
theorem reinsertBktM_eq : ∀ (b : Bkt K V) (raw : TRaw K V) (h : 0 < raw.buckets.size),
    (reinsertBktM b : StateT (TRaw K V) (Except ε) Unit) raw =
      .ok ((), { raw with buckets := (b.foldl (Raw₀.reinsertAux hash) ⟨raw.buckets, h⟩).1 })
  | .nil, raw, h => rfl
  | .cons k v t, raw, h => by
    simp only [reinsertBktM, bind, StateT.bind, Except.bind]
    rw [reinsertOneM_eq raw h k v]
    simp only
    have h' : 0 < (Raw₀.reinsertAux hash ⟨raw.buckets, h⟩ k v).1.size := by rw [reinsertAux_size]; exact h
    rw [reinsertBktM_eq t _ h']
    rfl

/-- Reinserting the buckets in order, as `expand` does. -/
def reinsertAllF (bs : List (Bkt K V)) (t : { d : Array (Bkt K V) // 0 < d.size }) :
    { d : Array (Bkt K V) // 0 < d.size } :=
  bs.foldl (fun t es => es.foldl (Raw₀.reinsertAux hash) t) t

omit [BEq K] in
theorem foldl_reinsert_size : ∀ (b : Bkt K V) (t : { d : Array (Bkt K V) // 0 < d.size }),
    (b.foldl (Raw₀.reinsertAux hash) t).1.size = t.1.size
  | .nil, _ => rfl
  | .cons k v r, t => by
    show (r.foldl (Raw₀.reinsertAux hash) (Raw₀.reinsertAux hash t k v)).1.size = _
    rw [foldl_reinsert_size r, reinsertAux_size]

omit [BEq K] in
theorem reinsertAllM_eq : ∀ (bs : List (Bkt K V)) (raw : TRaw K V) (h : 0 < raw.buckets.size),
    (reinsertAllM bs : StateT (TRaw K V) (Except ε) Unit) raw =
      .ok ((), { raw with buckets := (reinsertAllF bs ⟨raw.buckets, h⟩).1 })
  | [], raw, h => rfl
  | b :: bs, raw, h => by
    simp only [reinsertAllM, bind, StateT.bind, Except.bind]
    rw [reinsertBktM_eq b raw h]
    simp only
    have h' : 0 < (b.foldl (Raw₀.reinsertAux hash) ⟨raw.buckets, h⟩).1.size := by
      rw [foldl_reinsert_size]; exact h
    rw [reinsertAllM_eq bs _ h']
    rfl

theorem readFromM_eq (raw : TRaw K V) : ∀ (i : Nat),
    (readFromM raw.buckets.size i : StateT (TRaw K V) (Except ε) (List (Bkt K V))) raw =
      .ok (raw.buckets.toList.drop i, raw) := by
  intro i
  induction h : raw.buckets.size - i generalizing i with
  | zero =>
    rw [readFromM]
    have : ¬ i < raw.buckets.size := by omega
    simp only [this, if_false, pure, StateT.pure]
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ d ih =>
    rw [readFromM]
    have hi : i < raw.buckets.size := by omega
    simp only [hi, if_true, bind, StateT.bind, tGetB, Except.bind, pure, StateT.pure]
    rw [ih (i + 1) (by omega)]
    simp only
    have hi' : i < raw.buckets.toList.length := by simpa using hi
    rw [List.drop_eq_getElem_cons hi']
    simp [Array.getD, hi]
    rfl

omit [BEq K] in
/-- `Raw₀.expand.go`: the remaining buckets reinserted in order. -/
theorem expand_go_eq (source : Array (Bkt K V)) : ∀ (i : Nat) (target : { d : Array (Bkt K V) // 0 < d.size }),
    Raw₀.expand.go i source target = reinsertAllF (source.toList.drop i) target := by
  intro i
  induction h : source.size - i generalizing i source with
  | zero =>
    intro target
    rw [Raw₀.expand.go]
    have : ¬ i < source.size := by omega
    simp only [this, dite_false]
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ d ih =>
    intro target
    rw [Raw₀.expand.go]
    have hi : i < source.size := by omega
    simp only [hi, dite_true]
    rw [ih (source.set i .nil) (i + 1) (by simp; omega)]
    have hi' : i < source.toList.length := by simpa using hi
    rw [List.drop_eq_getElem_cons hi']
    have hd : (source.set i .nil).toList.drop (i + 1) = source.toList.drop (i + 1) := by
      simp only [Array.toList_set]
      rw [List.drop_set_of_lt]
      omega
    rw [hd]
    simp only [reinsertAllF, List.foldl_cons]
    simp

theorem expandM_eq (raw : TRaw K V) (h : 0 < raw.buckets.size) :
    (expandM : StateT (TRaw K V) (Except ε) Unit) raw =
      .ok ((), { raw with buckets := (Raw₀.expand ⟨raw.buckets, h⟩).1 }) := by
  simp only [expandM, bind, StateT.bind, Except.bind, tNB]
  rw [readFromM_eq raw 0]
  simp only [List.drop_zero, tRealloc]
  have h2 : 0 < (Array.replicate (raw.buckets.size * 2) (AssocList.nil : Bkt K V)).size := by simp; omega
  rw [reinsertAllM_eq _ _ h2]
  simp only [Raw₀.expand]
  rw [expand_go_eq]
  simp [Array.propagateMark]

theorem expandIfNecessaryM_eq (raw : TRaw K V) (h : 0 < raw.buckets.size) :
    (expandIfNecessaryM : StateT (TRaw K V) (Except ε) Unit) raw =
      .ok ((), (Raw₀.expandIfNecessary ⟨raw, h⟩).1) := by
  obtain ⟨sz, bs⟩ := raw
  simp only [expandIfNecessaryM, tSize, tNB, bind, StateT.bind, Except.bind]
  have hn : numBucketsForCapacity sz = sz * 4 / 3 := rfl
  by_cases hc : sz * 4 / 3 ≤ bs.size
  · simp only [hc, if_true, Raw₀.expandIfNecessary, hn]
    rfl
  · simp only [hc, if_false, Raw₀.expandIfNecessary, hn]
    rw [expandM_eq _ h]

theorem insertM_eq (m : Raw₀ K (fun _ => V)) (k : K) (v : V) :
    (insertM k v : StateT (TRaw K V) (Except ε) Unit) m.1 = .ok ((), (Raw₀.insert m k v).1) := by
  obtain ⟨⟨sz, bs⟩, h⟩ := m
  simp only [insertM, tNB, tGetB, bind, StateT.bind, Except.bind]
  rw [getD_mkIdx bs h k]
  simp only [Raw₀.insert]
  by_cases hc : (bs[(mkIdx bs.size h (hash k)).1.toNat]'(mkIdx bs.size h (hash k)).2).contains k = true
  · simp only [hc, if_true, tSetB]
    rw [setIB_mkIdx bs h k]
    split
    · simp [Array.uset, Array.set_set]
    · rename_i hn; exact absurd hc hn
  · simp only [hc, Bool.false_eq_true, if_false, tSetB, tSize, tSetSize, bind, StateT.bind, Except.bind]
    rw [setIB_mkIdx bs h k]
    split
    · rename_i hp; exact absurd hp hc
    exact expandIfNecessaryM_eq _ (by simpa using h)

theorem sizeM_eq (raw : TRaw K V) :
    (sizeM : StateT (TRaw K V) (Except ε) Nat) raw = .ok (raw.size, raw) := rfl

omit [BEq K] [Hashable K] in
theorem emptyM_eq (raw : TRaw K V) :
    (emptyM : StateT (TRaw K V) (Except ε) Unit) raw =
      .ok ((), (Raw₀.emptyWithCapacity (α := K) (β := fun _ => V) 8).1) := by
  simp only [emptyM, tRealloc, tSetSize, bind, StateT.bind, Except.bind, Raw₀.emptyWithCapacity]
  have : (numBucketsForCapacity 8).nextPowerOfTwo = 16 := by
    show Nat.nextPowerOfTwo 10 = 16
    simp only [Nat.nextPowerOfTwo]
    simp (config := { decide := true }) [Nat.nextPowerOfTwo.go]
  rw [this]

end

end ConPastel.Translator
