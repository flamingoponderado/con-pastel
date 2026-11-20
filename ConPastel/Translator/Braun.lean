/-!
# Persistent arrays: Braun trees

`Array α` is represented in CakeML by a Braun tree with its size (`A α`): the
CakeML store is append-only in the refinement judgement, so an array cannot
be updated in place, and a list (the representation through `Array.toList`)
makes every access and update O(n). A Braun tree gives O(log n) `get`, `set`
and `push`. The tree of a list is canonical (`A.ofList`): its shape depends
on the size only, so `toA` (the representation function) is injective and
the operations commute with it (`A.set_ofList`, `A.push_ofList`).
-/


namespace ConPastel.Braun

inductive T (α : Type) where
  | leaf
  | node (l : T α) (x : α) (r : T α)

variable {α : Type}

def size : T α → Nat
  | .leaf => 0
  | .node l _ r => 1 + size l + size r

def get? : T α → Nat → Option α
  | .leaf, _ => none
  | .node l x r, i =>
    if i = 0 then some x
    else if i % 2 = 1 then get? l (i / 2) else get? r (i / 2 - 1)

def set : T α → Nat → α → T α
  | .leaf, _, _ => .leaf
  | .node l x r, i, y =>
    if i = 0 then .node l y r
    else if i % 2 = 1 then .node (set l (i / 2) y) x r else .node l x (set r (i / 2 - 1) y)

/-- Add at index `n = size t` (the Braun "snoc"). -/
def snoc : T α → Nat → α → T α
  | .leaf, _, y => .node .leaf y .leaf
  | .node l x r, n, y =>
    if n % 2 = 1 then .node (snoc l (n / 2) y) x r else .node l x (snoc r (n / 2 - 1) y)

/-- The Braun invariant: sizes of the two children differ by at most one, left ≥ right. -/
def WF : T α → Prop
  | .leaf => True
  | .node l _ r => WF l ∧ WF r ∧ (size l = size r ∨ size l = size r + 1)

end ConPastel.Braun

namespace ConPastel.Braun
variable {α : Type}

/-- The canonical tree of a list: snoc each element. -/
def ofList (l : List α) : T α := l.foldl (fun t x => snoc t (size t) x) .leaf

theorem size_snoc : ∀ (t : T α) (n : Nat) (y : α), size (snoc t n y) = size t + 1
  | .leaf, _, _ => by simp [snoc, size]
  | .node l x r, n, y => by
    unfold snoc; split <;> simp only [size, size_snoc] <;> omega

theorem size_set : ∀ (t : T α) (i : Nat) (y : α), size (set t i y) = size t
  | .leaf, _, _ => by simp [set]
  | .node l x r, i, y => by
    unfold set; split
    · simp [size]
    · split <;> simp only [size, size_set]

theorem size_ofList_aux : ∀ (l : List α) (t : T α), size (l.foldl (fun t x => snoc t (size t) x) t) = size t + l.length
  | [], t => by simp
  | x :: xs, t => by simp only [List.foldl, size_ofList_aux xs, size_snoc]; simp; omega

theorem size_ofList (l : List α) : size (ofList l) = l.length := by
  simp [ofList, size_ofList_aux, size]


theorem get?_none : ∀ (t : T α) (i : Nat), WF t → size t ≤ i → get? t i = none
  | .leaf, _, _, _ => by simp [get?]
  | .node l x r, i, ⟨hl, hr, hs⟩, hi => by
    simp only [size] at hi
    unfold get?
    rw [if_neg (by omega)]
    split
    · exact get?_none l _ hl (by omega)
    · exact get?_none r _ hr (by omega)

theorem wf_snoc : ∀ (t : T α) (y : α), WF t → WF (snoc t (size t) y)
  | .leaf, _, _ => by simp [snoc, WF, size]
  | .node l x r, y, ⟨hl, hr, hs⟩ => by
    unfold snoc
    by_cases hodd : size (T.node l x r) % 2 = 1
    · rw [if_pos hodd]; simp only [size] at hodd ⊢
      have : size l = size r := by omega
      rw [show (1 + size l + size r) / 2 = size l by omega]
      exact ⟨wf_snoc l y hl, hr, by rw [size_snoc]; omega⟩
    · rw [if_neg hodd]; simp only [size] at hodd ⊢
      have : size l = size r + 1 := by omega
      rw [show (1 + size l + size r) / 2 - 1 = size r by omega]
      exact ⟨hl, wf_snoc r y hr, by rw [size_snoc]; omega⟩

theorem get?_snoc : ∀ (t : T α) (y : α) (i : Nat), WF t →
    get? (snoc t (size t) y) i = if i = size t then some y else get? t i
  | .leaf, y, i, _ => by
    simp only [snoc, size, get?]
    split <;> simp_all
  | .node l x r, y, i, ⟨hl, hr, hs⟩ => by
    unfold snoc
    by_cases hodd : size (T.node l x r) % 2 = 1
    · rw [if_pos hodd]; simp only [size] at hodd ⊢
      have : size l = size r := by omega
      rw [show (1 + size l + size r) / 2 = size l by omega]
      unfold get?
      by_cases h0 : i = 0
      · simp [h0]; omega
      · rw [if_neg h0, if_neg h0]
        split
        · rw [get?_snoc l y _ hl]
          by_cases hi : i = 1 + size l + size r
          · rw [if_pos (by omega), if_pos hi]
          · rw [if_neg (by omega), if_neg hi]
        · rw [if_neg (by omega)]
    · rw [if_neg hodd]; simp only [size] at hodd ⊢
      have : size l = size r + 1 := by omega
      rw [show (1 + size l + size r) / 2 - 1 = size r by omega]
      unfold get?
      by_cases h0 : i = 0
      · simp [h0]; omega
      · rw [if_neg h0, if_neg h0]
        split
        · rw [if_neg (by omega)]
        · rw [get?_snoc r y _ hr]
          by_cases hi : i = 1 + size l + size r
          · rw [if_pos (by omega), if_pos hi]
          · rw [if_neg (by omega), if_neg hi]

theorem wf_ofList_aux : ∀ (l : List α) (t : T α), WF t → WF (l.foldl (fun t x => snoc t (size t) x) t)
  | [], t, h => h
  | x :: xs, t, h => wf_ofList_aux xs _ (wf_snoc t x h)

theorem wf_ofList (l : List α) : WF (ofList l) := wf_ofList_aux l .leaf trivial

theorem get?_ofList_aux : ∀ (l : List α) (t : T α) (i : Nat), WF t →
    get? (l.foldl (fun t x => snoc t (size t) x) t) i =
      if i < size t then get? t i else l[i - size t]?
  | [], t, i, h => by
    simp only [List.foldl]
    split
    · rfl
    · rw [get?_none t i h (by omega)]; simp
  | x :: xs, t, i, h => by
    simp only [List.foldl]
    rw [get?_ofList_aux xs _ i (wf_snoc t x h), size_snoc, get?_snoc t x i h]
    by_cases h1 : i < size t
    · rw [if_pos (by omega), if_neg (by omega), if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : i = size t
      · subst h2; simp
      · rw [if_neg (by omega)]
        rw [show i - size t = (i - (size t + 1)) + 1 by omega]
        simp

theorem get?_ofList (l : List α) (i : Nat) : get? (ofList l) i = l[i]? := by
  rw [ofList, get?_ofList_aux l .leaf i trivial]; simp [size]


theorem wf_set : ∀ (t : T α) (i : Nat) (y : α), WF t → WF (set t i y)
  | .leaf, _, _, h => h
  | .node l x r, i, y, ⟨hl, hr, hs⟩ => by
    unfold set
    by_cases h0 : i = 0
    · rw [if_pos h0]; exact ⟨hl, hr, hs⟩
    · rw [if_neg h0]
      by_cases ho : i % 2 = 1
      · rw [if_pos ho]; exact ⟨wf_set l _ y hl, hr, by rw [size_set]; exact hs⟩
      · rw [if_neg ho]; exact ⟨hl, wf_set r _ y hr, by rw [size_set]; exact hs⟩

theorem get?_set : ∀ (t : T α) (i j : Nat) (y : α),
    get? (set t i y) j = if i = j ∧ (get? t j).isSome then some y else get? t j
  | .leaf, _, _, _ => by simp [set, get?]
  | .node l x r, i, j, y => by
    unfold set
    by_cases h0 : i = 0
    · rw [if_pos h0]; subst h0
      unfold get?
      by_cases hj : j = 0
      · simp [hj]
      · simp [hj]; intro h; omega
    · rw [if_neg h0]
      by_cases ho : i % 2 = 1
      · rw [if_pos ho]
        unfold get?
        by_cases hj : j = 0
        · simp [hj]; omega
        · simp only [hj, if_false]
          by_cases hjo : j % 2 = 1
          · rw [if_pos hjo, if_pos hjo, get?_set l]
            by_cases hij : i = j
            · subst hij; simp
            · rw [if_neg (by omega), if_neg (by omega)]
          · rw [if_neg hjo, if_neg hjo, if_neg (by omega)]
      · rw [if_neg ho]
        unfold get?
        by_cases hj : j = 0
        · simp [hj]; omega
        · simp only [hj, if_false]
          by_cases hjo : j % 2 = 1
          · rw [if_pos hjo, if_pos hjo, if_neg (by omega)]
          · rw [if_neg hjo, if_neg hjo, get?_set r]
            by_cases hij : i = j
            · subst hij; simp
            · rw [if_neg (by omega), if_neg (by omega)]

theorem get?_some_iff : ∀ (t : T α) (i : Nat), WF t → ((get? t i).isSome ↔ i < size t)
  | .leaf, _, _ => by simp [get?, size]
  | .node l x r, i, ⟨hl, hr, hs⟩ => by
    unfold get?; simp only [size]
    by_cases h0 : i = 0
    · simp [h0]; omega
    · rw [if_neg h0]
      split
      · rw [get?_some_iff l _ hl]; omega
      · rw [get?_some_iff r _ hr]; omega

/-- Two well-formed trees with the same entries are equal (the shape is fixed by the size). -/
theorem ext : ∀ (a b : T α), WF a → WF b → (∀ i, get? a i = get? b i) → a = b
  | .leaf, .leaf, _, _, _ => rfl
  | .leaf, .node l x r, _, _, h => by have := h 0; simp [get?] at this
  | .node l x r, .leaf, _, _, h => by have := h 0; simp [get?] at this
  | .node l x r, .node l' x' r', ⟨hl, hr, _⟩, ⟨hl', hr', _⟩, h => by
    have hx : x = x' := by have := h 0; simpa [get?] using this
    have hL : l = l' := ext l l' hl hl' fun j => by
      have := h (2 * j + 1)
      have h1 : ¬ 2 * j + 1 = 0 := by omega
      have h2 : (2 * j + 1) % 2 = 1 := by omega
      simp only [get?, h1, h2, if_false, if_true, show (2 * j + 1) / 2 = j by omega] at this
      exact this
    have hR : r = r' := ext r r' hr hr' fun j => by
      have := h (2 * j + 2)
      have h1 : ¬ 2 * j + 2 = 0 := by omega
      have h2 : ¬ (2 * j + 2) % 2 = 1 := by omega
      simp only [get?, h1, h2, if_false, show (2 * j + 2) / 2 - 1 = j by omega] at this
      exact this
    rw [hx, hL, hR]

theorem set_ofList (l : List α) (i : Nat) (y : α) : set (ofList l) i y = ofList (l.set i y) := by
  apply ext _ _ (wf_set _ _ _ (wf_ofList l)) (wf_ofList _)
  intro j
  rw [get?_set, get?_ofList, get?_ofList, List.getElem?_set]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < l.length
    · simp [hi]
    · simp [hi, List.getElem?_eq_none (by omega : l.length ≤ i)]
  · simp [hij]

theorem snoc_ofList (l : List α) (y : α) : snoc (ofList l) l.length y = ofList (l ++ [y]) := by
  simp [ofList, List.foldl_append, ← size_ofList l]

/-- The entries in index order. -/
def toList (t : T α) : List α := (List.range (size t)).filterMap (get? t)

theorem range_filterMap_take (l : List α) : ∀ n, n ≤ l.length →
    (List.range n).filterMap (fun i => l[i]?) = l.take n
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.filterMap_append, range_filterMap_take l n (by omega)]
    have hn : n < l.length := by omega
    rw [List.take_succ, List.getElem?_eq_getElem hn]
    simp only [List.filterMap_cons, List.filterMap_nil, List.getElem?_eq_getElem hn, Option.toList_some]

theorem range_filterMap_getElem? (l : List α) :
    (List.range l.length).filterMap (fun i => l[i]?) = l := by
  rw [range_filterMap_take l l.length (Nat.le_refl _), List.take_length]

theorem toList_ofList (l : List α) : toList (ofList l) = l := by
  have : get? (ofList l) = fun i => l[i]? := funext (get?_ofList l)
  rw [toList, size_ofList, this]
  exact range_filterMap_getElem? l

end ConPastel.Braun

namespace ConPastel.Braun
variable {α : Type}

/-- A persistent array: the size and the canonical tree. -/
structure A (α : Type) where
  n : Nat
  t : T α

/-- The canonical representation of a list. -/
def A.ofList (l : List α) : A α := ⟨l.length, Braun.ofList l⟩
def A.toList (a : A α) : List α := Braun.toList a.t

theorem A.toList_ofList (l : List α) : (A.ofList l).toList = l := Braun.toList_ofList l

def A.set (a : A α) (i : Nat) (y : α) : A α := ⟨a.n, Braun.set a.t i y⟩
def A.push (a : A α) (y : α) : A α := ⟨a.n + 1, Braun.snoc a.t a.n y⟩
def A.get? (a : A α) (i : Nat) : Option α := Braun.get? a.t i

theorem A.set_ofList (l : List α) (i : Nat) (y : α) : (A.ofList l).set i y = A.ofList (l.set i y) := by
  simp [A.set, A.ofList, Braun.set_ofList]

theorem A.push_ofList (l : List α) (y : α) : (A.ofList l).push y = A.ofList (l ++ [y]) := by
  simp [A.push, A.ofList, Braun.snoc_ofList]

theorem A.get?_ofList (l : List α) (i : Nat) : (A.ofList l).get? i = l[i]? := by
  simp [A.get?, A.ofList, Braun.get?_ofList]

end ConPastel.Braun

namespace ConPastel.Braun
variable {α : Type}

theorem A.ofList_toList_ofList (l : List α) : A.ofList (A.ofList l).toList = A.ofList l := by
  rw [A.toList_ofList]

/-- The representation of an array. -/
def toA (a : Array α) : A α := A.ofList a.toList

/-- The array of a canonical tree (`h`): its representation is the tree itself. -/
def ofAC (t : A α) (_h : A.ofList t.toList = t) : Array α := ⟨t.toList⟩

theorem toA_ofAC (t : A α) (h : A.ofList t.toList = t) : toA (ofAC t h) = t := by
  simp only [toA, ofAC]; exact h

theorem toList_toA (a : Array α) : a.toList = (toA a).toList := by
  rw [toA, A.toList_ofList]

theorem toA_inj {a b : Array α} (h : toA a = toA b) : a = b := by
  apply Array.ext'; rw [toList_toA a, toList_toA b, h]

theorem canon_toA (a : Array α) : A.ofList (toA a).toList = toA a := A.ofList_toList_ofList _

end ConPastel.Braun
