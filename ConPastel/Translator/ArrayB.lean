import ConPastel.Translator.Braun
import ConPastel.Translator.Meta.Primitive

/-!
# `Array` operations on the Braun representation

Each operation the translation reaches is replaced (`cake_replace`) by the
same operation on the array's tree (`toA`), with the result put back through
`ofAC` (the tree is canonical, so the translation reads `toA (ofAC t h)` as
the tree `t` itself). Operations not replaced here still translate, through
`Array.mk`/`Array.toList` (O(n) conversions).
-/

namespace ConPastel.Braun
variable {α : Type}

theorem toA_toList (a : Array α) : (toA a).toList = a.toList := by
  rw [toList_toA a]

theorem toA_n (a : Array α) : (toA a).n = a.size := by
  simp [toA, A.ofList]

theorem toA_get? (a : Array α) (i : Nat) : (toA a).get? i = a[i]? := by
  simp [toA, A.get?_ofList]

/-- `Array.size`: the stored size. -/
def arrSize (a : Array α) : Nat := (toA a).n

theorem size_eq (a : Array α) : a.size = arrSize a := (toA_n a).symm

theorem getInternal_isSome (a : Array α) (i : Nat) (h : i < a.size) :
    ((toA a).get? i).isSome = true := by
  rw [toA_get?]; simp [h]

/-- `Array.getInternal`: the tree lookup. -/
def arrGet (a : Array α) (i : Nat) (h : i < a.size) : α :=
  ((toA a).get? i).get (getInternal_isSome a i h)

theorem getInternal_eq (a : Array α) (i : Nat) (h : i < a.size) : a.getInternal i h = arrGet a i h := by
  have h2 : (toA a).get? i = some a[i] := by rw [toA_get?, Array.getElem?_eq_getElem h]
  unfold arrGet
  simp only [h2, Option.get_some]
  rfl

/-- `Array.get!Internal`: the tree lookup, the default out of range. -/
def arrGetBang [Inhabited α] (a : Array α) (i : Nat) : α := ((toA a).get? i).getD default

theorem getBang_eq [Inhabited α] (a : Array α) (i : Nat) : a.get!Internal i = arrGetBang a i := by
  unfold arrGetBang; rw [toA_get?]
  unfold Array.get!Internal Array.getD
  split
  · rename_i h; rw [Array.getElem?_eq_getElem h]; rfl
  · rename_i h; rw [Array.getElem?_eq_none (by omega)]; rfl

theorem canon_set (a : Array α) (i : Nat) (y : α) :
    A.ofList ((toA a).set i y).toList = (toA a).set i y := by
  rw [toA, A.set_ofList, A.ofList_toList_ofList]

theorem canon_push (a : Array α) (y : α) :
    A.ofList ((toA a).push y).toList = (toA a).push y := by
  rw [toA, A.push_ofList, A.ofList_toList_ofList]

/-- `Array.set`: the tree update. -/
def arrSet (a : Array α) (i : Nat) (y : α) (_h : i < a.size) : Array α :=
  ofAC ((toA a).set i y) (canon_set a i y)

/-- `Array.setIfInBounds`: the tree update (a no-op out of range, as `List.set`). -/
def arrSetIB (a : Array α) (i : Nat) (y : α) : Array α :=
  ofAC ((toA a).set i y) (canon_set a i y)

/-- `Array.push`: the tree snoc. -/
def arrPush (a : Array α) (y : α) : Array α :=
  ofAC ((toA a).push y) (canon_push a y)

theorem toList_set_toA (a : Array α) (i : Nat) (y : α) : ((toA a).set i y).toList = a.toList.set i y := by
  rw [toA, A.set_ofList, A.toList_ofList]

theorem set_eq (a : Array α) (i : Nat) (y : α) (h : i < a.size) : a.set i y h = arrSet a i y h := by
  apply Array.ext'
  simp [arrSet, ofAC, toList_set_toA]

theorem setIfInBounds_eq (a : Array α) (i : Nat) (y : α) : a.setIfInBounds i y = arrSetIB a i y := by
  apply Array.ext'
  simp only [arrSetIB, ofAC, toList_set_toA]
  simp [Array.setIfInBounds]
  split
  · simp
  · rename_i h; rw [List.set_eq_of_length_le (by simpa using h)]

theorem push_eq (a : Array α) (y : α) : a.push y = arrPush a y := by
  apply Array.ext'
  simp [arrPush, ofAC, toA, A.push_ofList, A.toList_ofList]

theorem canon_ofList (l : List α) : A.ofList (A.ofList l).toList = A.ofList l := A.ofList_toList_ofList l

/-- `Array.replicate`: the tree of the list. -/
def arrReplicate (n : Nat) (y : α) : Array α :=
  ofAC (A.ofList (List.replicate n y)) (canon_ofList _)

theorem replicate_eq (n : Nat) (y : α) : Array.replicate n y = arrReplicate n y := by
  apply Array.ext'
  simp [arrReplicate, ofAC, A.toList_ofList]

/-- `ofList` with the size counted along (`ofList` recomputes `size`, a walk of
the tree, at every element). -/
def ofListGo : List α → T α → Nat → T α
  | [], t, _ => t
  | x :: xs, t, n => ofListGo xs (snoc t n x) (n + 1)

def ofListF (l : List α) : T α := ofListGo l .leaf 0

theorem ofListGo_eq : ∀ (l : List α) (t : T α),
    ofListGo l t (size t) = l.foldl (fun t x => snoc t (size t) x) t
  | [], _ => rfl
  | x :: xs, t => by
    simp only [ofListGo, List.foldl]
    rw [← size_snoc t (size t) x, ofListGo_eq xs]

theorem ofList_eq_F (l : List α) : ofList l = ofListF l := by
  rw [ofListF, ofList, ← ofListGo_eq l .leaf]; rfl

end ConPastel.Braun

cake_replace ConPastel.Braun.ofList ConPastel.Braun.ofListF ConPastel.Braun.ofList_eq_F
cake_replace Array.size ConPastel.Braun.arrSize ConPastel.Braun.size_eq
cake_replace Array.getInternal ConPastel.Braun.arrGet ConPastel.Braun.getInternal_eq
cake_replace Array.get!Internal ConPastel.Braun.arrGetBang ConPastel.Braun.getBang_eq
cake_replace Array.set ConPastel.Braun.arrSet ConPastel.Braun.set_eq
cake_replace Array.setIfInBounds ConPastel.Braun.arrSetIB ConPastel.Braun.setIfInBounds_eq
cake_replace Array.push ConPastel.Braun.arrPush ConPastel.Braun.push_eq
cake_replace Array.replicate ConPastel.Braun.arrReplicate ConPastel.Braun.replicate_eq
