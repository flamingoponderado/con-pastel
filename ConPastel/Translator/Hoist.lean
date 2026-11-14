import ConPastel.Translator.Replace
import ConLeche.Frontend.NatOpGround

/-! # A `while`-free `ConLeche.Frontend.hoistTargets`

The DFS closure loop of `hoistTargets` is a `while` (`Lean.Loop.forIn`, defined
through `repeatM`).  `closeLoop` is the same loop as a well-founded recursive
function; `hoistTargets'` uses it and `hoistTargets_eq` proves the two equal. -/

namespace ConPastel.Impl

open ConLeche

/-- Has record `k` already been assigned a target `≤ i`? -/
def doneAt (target : Std.HashMap Nat Nat) (i k : Nat) : Bool :=
  match target[k]? with
  | some t => decide (t ≤ i)
  | none => false

/-- The inner `for n in used ds[k]!` loop of the closure. -/
def pushAll (used : Declaration → Array Name) (ds : Array Declaration)
    (idx : Std.HashMap Name Nat) (i k : Nat) (stack : Array Nat) : Array Nat :=
  (used ds[k]!).foldl (fun s n =>
    match idx[n]? with
    | some m => if (decide (m > i) && m != k) = true then s.push m else s
    | none => s) stack

/-- The largest `(used ds[k]!).size` for `k < B`. -/
def maxUsed (used : Declaration → Array Name) (ds : Array Declaration) (B : Nat) : Nat :=
  (List.range B).foldl (fun acc k => max acc (used ds[k]!).size) 0

/-- The termination measure of the closure loop. -/
def closeMeasure (used : Declaration → Array Name) (ds : Array Declaration) (B i : Nat)
    (target : Std.HashMap Nat Nat) (stack : Array Nat) : Nat :=
  (List.range B).countP (fun k => !doneAt target i k) * (maxUsed used ds B + 1) + stack.size

/-- One more than the largest value of `idx` (`0` when empty). -/
def idxBound (idx : Std.HashMap Name Nat) : Nat :=
  idx.fold (fun acc _ v => max acc (v + 1)) 0

theorem foldl_max_ge {α : Type _} (f : α → Nat) :
    ∀ (l : List α) (acc : Nat), acc ≤ l.foldl (fun a y => max a (f y)) acc ∧
      ∀ x ∈ l, f x ≤ l.foldl (fun a y => max a (f y)) acc
  | [], acc => ⟨Nat.le_refl _, by simp⟩
  | y :: l, acc => by
    obtain ⟨h1, h2⟩ := foldl_max_ge f l (max acc (f y))
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, ?_⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 x hx

theorem lt_idxBound (idx : Std.HashMap Name Nat) (n : Name) (m : Nat) (h : idx[n]? = some m) :
    m < idxBound idx := by
  unfold idxBound
  rw [Std.HashMap.fold_eq_foldl_toList]
  have hm : (n, m) ∈ idx.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h
  have := (foldl_max_ge (fun p : Name × Nat => p.2 + 1) idx.toList 0).2 _ hm
  simp at this
  omega

theorem le_maxUsed (used : Declaration → Array Name) (ds : Array Declaration) (B k : Nat)
    (hk : k < B) : (used ds[k]!).size ≤ maxUsed used ds B :=
  (foldl_max_ge (fun k => (used ds[k]!).size) (List.range B) 0).2 k (by simpa using hk)

theorem size_pushAll (used : Declaration → Array Name) (ds : Array Declaration)
    (idx : Std.HashMap Name Nat) (i k : Nat) (stack : Array Nat) :
    (pushAll used ds idx i k stack).size ≤ stack.size + (used ds[k]!).size := by
  unfold pushAll
  refine Array.foldl_induction (motive := fun j (s : Array Nat) => s.size ≤ stack.size + j)
    (by simp) ?_
  intro j s hs
  split
  · split <;> (try simp only [Array.size_push]) <;> omega
  · omega

theorem countP_lt {α : Type _} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, q x = true → p x = true) → (∃ x ∈ l, p x = true ∧ q x = false) →
      l.countP q < l.countP p
  | [], _, ⟨_, hx, _⟩ => by simp at hx
  | y :: l, hle, ⟨x, hx, hpx, hqx⟩ => by
    have hle' : ∀ x ∈ l, q x = true → p x = true := fun x hx => hle x (by simp [hx])
    have mono : l.countP q ≤ l.countP p := List.countP_mono_left hle'
    have hy := hle y (by simp)
    simp only [List.countP_cons]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [hpx, hqx]; simp; omega
    · have := countP_lt p q l hle' ⟨x, hx, hpx, hqx⟩
      cases hpy : p y <;> cases hqy : q y <;> simp_all; omega

theorem doneAt_insert (target : Std.HashMap Nat Nat) (i k x : Nat) (h : doneAt target i x = true) :
    doneAt (target.insert k i) i x = true := by
  unfold doneAt at *
  rw [Std.HashMap.getElem?_insert]
  by_cases hkx : k = x
  · simp [hkx]
  · simpa [hkx] using h

theorem doneAt_insert_self (target : Std.HashMap Nat Nat) (i k : Nat) :
    doneAt (target.insert k i) i k = true := by
  simp [doneAt]

theorem measure_skip (used : Declaration → Array Name) (ds : Array Declaration) (B i : Nat)
    (target : Std.HashMap Nat Nat) (stack : Array Nat) (h : stack.size > 0) :
    closeMeasure used ds B i target stack.pop < closeMeasure used ds B i target stack := by
  unfold closeMeasure; simp only [Array.size_pop]; omega

theorem measure_step (used : Declaration → Array Name) (ds : Array Declaration)
    (idx : Std.HashMap Name Nat) (B i : Nat)
    (target : Std.HashMap Nat Nat) (stack : Array Nat) (h : stack.size > 0) (k : Nat)
    (hk : k < B) (hd : doneAt target i k = false) :
    closeMeasure used ds B i (target.insert k i) (pushAll used ds idx i k stack.pop) <
      closeMeasure used ds B i target stack := by
  unfold closeMeasure
  have hc := countP_lt (fun x => !doneAt target i x) (fun x => !doneAt (target.insert k i) i x)
    (List.range B)
    (by
      intro x _ hx
      cases hdx : doneAt target i x
      · rfl
      · simp [doneAt_insert target i k x hdx] at hx)
    ⟨k, by simpa using hk, by simp [hd], by simp [doneAt_insert_self]⟩
  have hs := size_pushAll used ds idx i k stack.pop
  have hw := le_maxUsed used ds B k hk
  simp only [Array.size_pop] at hs
  generalize (List.range B).countP (fun x => !doneAt target i x) = c at *
  generalize (List.range B).countP (fun x => !doneAt (target.insert k i) i x) = c' at *
  generalize maxUsed used ds B = W at *
  generalize (pushAll used ds idx i k stack.pop).size = s' at *
  have : (c' + 1) * (W + 1) ≤ c * (W + 1) := Nat.mul_le_mul_right _ hc
  rw [Nat.succ_mul] at this
  omega

/-- The DFS closure loop of `hoistTargets` as a well-founded recursive function.
`B` bounds every stack element (they are all `idx` values); processing is guarded
by `k < B` so that termination needs no invariant. -/
def closeLoop (used : Declaration → Array Name) (ds : Array Declaration)
    (idx : Std.HashMap Name Nat) (i B : Nat) (target : Std.HashMap Nat Nat)
    (stack : Array Nat) : Std.HashMap Nat Nat :=
  if h : stack.size > 0 then
    let k := stack[stack.size - 1]
    if hd : doneAt target i k = true then
      closeLoop used ds idx i B target stack.pop
    else if hk : k < B then
      closeLoop used ds idx i B (target.insert k i) (pushAll used ds idx i k stack.pop)
    else target
  else target
termination_by closeMeasure used ds B i target stack
decreasing_by
  · exact measure_skip used ds B i target stack h
  · exact measure_step used ds idx B i target stack h _ hk (by simpa using hd)

/-- The original `while` loop, verbatim. -/
def whileLoop (used : Declaration → Array Name) (ds : Array Declaration)
    (idx : Std.HashMap Name Nat) (i : Nat) (target : Std.HashMap Nat Nat)
    (stack : Array Nat) : Std.HashMap Nat Nat := Id.run do
  let mut target := target
  let mut stack := stack
  while h : stack.size > 0 do
    let k := stack[stack.size - 1]
    stack := stack.pop
    match target[k]? with
    | some t => if t ≤ i then continue
    | none => pure ()
    target := target.insert k i
    for n in used ds[k]! do
      if let some m := idx[n]? then
        if m > i && m != k then stack := stack.push m
  return target

theorem forIn_pushAll (used : Declaration → Array Name) (ds : Array Declaration)
    (idx : Std.HashMap Name Nat) (i k : Nat) (stack : Array Nat) :
    (forIn (m := Id) (used ds[k]!) stack fun n (s : Array Nat) =>
      match idx[n]? with
      | some m =>
        if (decide (m > i) && m != k) = true then pure (ForInStep.yield (s.push m))
        else pure (ForInStep.yield s)
      | _ => pure (ForInStep.yield s)) = pure (pushAll used ds idx i k stack) := by
  unfold pushAll
  rw [← Array.forIn_pure_yield_eq_foldl]
  congr; funext n s
  cases idx[n]? with
  | none => rfl
  | some m => dsimp only; split <;> rfl

theorem pushAll_bound (used : Declaration → Array Name) (ds : Array Declaration)
    (idx : Std.HashMap Name Nat) (i k B : Nat)
    (hB : ∀ (n : Name) (m : Nat), idx[n]? = some m → m < B) (stack : Array Nat) (hs : ∀ x ∈ stack, x < B) :
    ∀ x ∈ pushAll used ds idx i k stack, x < B := by
  unfold pushAll
  refine Array.foldl_induction (motive := fun _ (s : Array Nat) => ∀ x ∈ s, x < B) hs ?_
  intro j s h
  split
  · rename_i m hm
    split
    · intro x hx
      simp only [Array.mem_push] at hx
      rcases hx with hx | rfl
      · exact h x hx
      · exact hB _ _ hm
    · exact h
  · exact h

theorem whileLoop_step (used : Declaration → Array Name) (ds : Array Declaration)
    (idx : Std.HashMap Name Nat) (i : Nat) 
    (target : Std.HashMap Nat Nat) (stack : Array Nat) :
    whileLoop used ds idx i target stack =
      if h : stack.size > 0 then
        if doneAt target i stack[stack.size - 1] = true then
          whileLoop used ds idx i target stack.pop
        else whileLoop used ds idx i (target.insert stack[stack.size - 1] i)
          (pushAll used ds idx i stack[stack.size - 1] stack.pop)
      else target := by
  conv => lhs; unfold whileLoop
  simp only [Id.run]
  rw [show ∀ b f, (forIn (m := Id) Lean.Loop.mk b f) = Lean.Loop.forIn Lean.Loop.mk b f from fun _ _ => rfl]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  by_cases h : stack.size > 0
  · simp only [h, dite_true]
    rw [forIn_pushAll]
    unfold doneAt
    split
    · rename_i t ht
      simp only [ht]
      by_cases ht' : t ≤ i
      · simp only [ht', ite_true, decide_true]; rfl
      · simp only [ht', ite_false, decide_false, Bool.false_eq_true]; rfl
    · rename_i ht
      simp only [ht, Bool.false_eq_true, ite_false]; rfl
  · simp only [h, dite_false]; rfl
theorem whileLoop_aux (used : Declaration → Array Name) (ds : Array Declaration)
    (idx : Std.HashMap Name Nat) (i B : Nat) (hB : ∀ (n : Name) (m : Nat), idx[n]? = some m → m < B)
    (target : Std.HashMap Nat Nat) (stack : Array Nat) (hs : ∀ x ∈ stack, x < B) :
    whileLoop used ds idx i target stack = closeLoop used ds idx i B target stack := by
  rw [whileLoop_step, closeLoop]
  by_cases h : stack.size > 0
  · simp only [h, dite_true]
    have hkB : stack[stack.size - 1] < B := hs _ (Array.getElem_mem _)
    have hpop : ∀ x ∈ stack.pop, x < B := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hx
      rw [Array.getElem_pop]
      exact hs _ (Array.getElem_mem _)
    by_cases hd : doneAt target i stack[stack.size - 1] = true
    · simp only [hd, ite_true, dite_true]
      exact whileLoop_aux used ds idx i B hB target stack.pop hpop
    · simp only [hd, hkB, dite_false, dite_true, Bool.false_eq_true, ite_false]
      exact whileLoop_aux used ds idx i B hB _ _ (pushAll_bound used ds idx i _ B hB _ hpop)
  · simp only [h, dite_false]
termination_by closeMeasure used ds B i target stack
decreasing_by
  · exact measure_skip used ds B i target stack h
  · exact measure_step used ds idx B i target stack h _ hkB (by simpa using hd)

theorem whileLoop_eq (used : Declaration → Array Name) (ds : Array Declaration)
    (idx : Std.HashMap Name Nat) (i j : Nat) (target : Std.HashMap Nat Nat) :
    whileLoop used ds idx i target #[j] =
      closeLoop used ds idx i (max (idxBound idx) (j + 1)) target #[j] := by
  apply whileLoop_aux
  · intro n m h
    exact Nat.lt_of_lt_of_le (lt_idxBound idx n m h) (Nat.le_max_left _ _)
  · intro x hx
    simp at hx; subst hx
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)

/-- `hoistTargets` with the `while` loop factored out into `whileLoop`. -/
def hoistTargetsW (used : Declaration → Array Name) (ds : Array Declaration) :
    Std.HashMap Nat Nat := Id.run do
  let mut idx : Std.HashMap Name Nat := {}
  for i in [0:ds.size] do
    for n in ds[i]!.names do
      if !idx.contains n then idx := idx.insert n i
  let mut target : Std.HashMap Nat Nat := {}
  for i in [0:ds.size] do
    let some c := Frontend.isNatOpRecord ds[i]! | continue
    for g in natOpDeps c do
      let some j := idx[g]? | continue
      unless j > i do continue
      target := whileLoop used ds idx i target #[j]
  return target

/-- **`hoistTargets` without `while`.** -/
def hoistTargets' (used : Declaration → Array Name) (ds : Array Declaration) :
    Std.HashMap Nat Nat := Id.run do
  let mut idx : Std.HashMap Name Nat := {}
  for i in [0:ds.size] do
    for n in ds[i]!.names do
      if !idx.contains n then idx := idx.insert n i
  let bound := idxBound idx
  let mut target : Std.HashMap Nat Nat := {}
  for i in [0:ds.size] do
    let some c := Frontend.isNatOpRecord ds[i]! | continue
    for g in natOpDeps c do
      let some j := idx[g]? | continue
      unless j > i do continue
      target := closeLoop used ds idx i (max bound (j + 1)) target #[j]
  return target

theorem hoistTargets_eqW (used : Declaration → Array Name) (ds : Array Declaration) :
    Frontend.hoistTargets used ds = hoistTargetsW used ds := rfl

theorem hoistTargets_eq (used : Declaration → Array Name) (ds : Array Declaration) :
    Frontend.hoistTargets used ds = hoistTargets' used ds := by
  rw [hoistTargets_eqW]
  unfold hoistTargetsW hoistTargets'
  simp only [whileLoop_eq]

end ConPastel.Impl

cake_replace ConLeche.Frontend.hoistTargets ConPastel.Impl.hoistTargets' ConPastel.Impl.hoistTargets_eq
