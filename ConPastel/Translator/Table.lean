import ConPastel.Translator.Push

/-!
# Hash tables updated in place

A `Std.HashMap` value is a `Std.DHashMap.Raw`: a size and an array of buckets
(association lists). Here such a raw map is a state held in the store exactly
as it is in Lean, so that its operations can update it in place:

* the **table cell** `tl` is a CakeML array of two entries, the location of
  the bucket array and the size;
* the **bucket array** is a CakeML array with one value per bucket.

The state relation `tblRel` owns both cells. The bucket array is reallocated
when the table grows, so ownership depends on the store (`StateRel.owns`).

The primitives below read the number of buckets, the size, and a bucket;
write a bucket in place and the size; and replace the bucket array by a fresh
one. The map operations are written with them (`ConPastel.Translator.HashMapM`),
step for step as Std writes its own, so that each is *equal* to Std's.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL

/-- A raw hash map with values of a fixed type. -/
abbrev TRaw (K V : Type) := Std.DHashMap.Raw K (fun _ => V)
/-- One of its buckets. -/
abbrev Bkt (K V : Type) := Std.DHashMap.Internal.AssocList K (fun _ => V)

/-- The raw map held in the table cell `tl`: its bucket array `a`, one value per
bucket (`BI`), and its size. -/
def tblRel {K V : Type} (BI : RefInv (Bkt K V)) (tl : Nat) : StateRel (TRaw K V) where
  owns r l := l = tl ∨ ∃ b n, r[tl]? = some (.varray [.loc b l, .litv (.intLit n)])
  rel st r := ∃ b a bs, r[tl]? = some (.varray [.loc b a, .litv (.intLit st.size)]) ∧ a ≠ tl ∧
    r[a]? = some (.varray bs) ∧ List.Forall₂ BI st.buckets.toList bs
  inRange st r h l hl := by
    obtain ⟨b, a, bs, ht, _, ha, _⟩ := h
    rcases hl with rfl | ⟨b', n, ht'⟩
    · exact (List.getElem?_eq_some_iff.mp ht).1
    · rw [ht] at ht'
      simp only [Option.some.injEq, StoreValue.varray.injEq, List.cons.injEq, Value.loc.injEq] at ht'
      obtain ⟨⟨_, rfl⟩, _⟩ := ht'
      exact (List.getElem?_eq_some_iff.mp ha).1
  stable st r r' h _ hsame := by
    obtain ⟨b, a, bs, ht, hne, ha, hF⟩ := h
    refine ⟨b, a, bs, by rw [hsame _ (Or.inl rfl), ht], hne, ?_, hF⟩
    rw [hsame a (Or.inr ⟨b, st.size, ht⟩), ha]
  ownsStable st r r' h _ hsame l _ ho := by
    rcases ho with rfl | ⟨b, n, ht'⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨b, n, by rw [← hsame _ (Or.inl rfl), ht']⟩

/-! ## The primitives, on the raw map -/

section
variable {K V ε : Type}

/-- The number of buckets. -/
def tNB : StateT (TRaw K V) (Except ε) Nat := fun st => .ok (st.buckets.size, st)
/-- The size. -/
def tSize : StateT (TRaw K V) (Except ε) Nat := fun st => .ok (st.size, st)
/-- Bucket `i` (empty out of range). -/
def tGetB (i : Nat) : StateT (TRaw K V) (Except ε) (Bkt K V) :=
  fun st => .ok (st.buckets.getD i .nil, st)
/-- Write bucket `i` (nothing out of range). -/
def tSetB (i : Nat) (x : Bkt K V) : StateT (TRaw K V) (Except ε) Unit :=
  fun st => .ok ((), { st with buckets := st.buckets.setIfInBounds i x })
/-- Set the size. -/
def tSetSize (n : Nat) : StateT (TRaw K V) (Except ε) Unit :=
  fun st => .ok ((), { st with size := n })
/-- Replace the buckets by `n` empty ones. -/
def tRealloc (n : Nat) : StateT (TRaw K V) (Except ε) Unit :=
  fun st => .ok ((), { st with buckets := Array.replicate n .nil })

end

theorem nsl_self {ns : Namespace ModN VarN Value} {x : VarN} {v : Value} :
    nsLookup (nsOptBind (some x) v ns) (.short x) = some v := by
  simp [nsOptBind, nsLookup_nsBind_short]

theorem nsl_ne {ns : Namespace ModN VarN Value} {x h : VarN} {v w : Value}
    (hne : x ≠ h) (hh : nsLookup ns (.short h) = some w) :
    nsLookup (nsOptBind (some x) v ns) (.short h) = some w := by
  simp [nsOptBind, nsLookup_nsBind_short, Ne.symm hne, hh]

/-! ## Evaluation of the cell accesses -/

theorem evaluate_asub_lit {τ : Type} (s : State τ) {env : SemEnv Value} {h : Ident ModN VarN}
    {b : Bool} {tl k : Nat} {vs : List Value} (hh : nsLookup env.v h = some (.loc b tl))
    (hv : s.refs[tl]? = some (.varray vs)) (hk : k < vs.length) :
    evaluate s env [.app .asub [.var h, .lit (.intLit k)]] = (s, .val [vs[k]]) := by
  have hargs : evaluate s env [.lit (.intLit k), .var h] = (s, .val [.litv (.intLit k), .loc b tl]) :=
    evaluate_cons_val (s₁ := s) (by simp [evaluate]) (by simp [evaluate, hh])
  have := evaluate_app_simple (s := s) (s₁ := s) (env := env) (op := .asub)
    (args := [.var h, .lit (.intLit k)]) (vs := [.litv (.intLit k), .loc b tl]) (refs := s.refs)
    (ffi := s.ffi) (r := .val vs[k]) (by simpa using hargs) rfl
    (by
      have hneg : ¬ ((k : Int) < 0) := by omega
      simp [doApp, doAppBasic, doAppNumericCore, storeLookup, hv, readIndexed, hneg,
        List.getElem?_eq_getElem hk])
  simpa [listResult] using this

theorem evaluate_aupdate_lit {τ : Type} (s : State τ) {env : SemEnv Value} {h xv : Ident ModN VarN}
    {b : Bool} {tl k : Nat} {vs : List Value} {x : Value} (hh : nsLookup env.v h = some (.loc b tl))
    (hx : nsLookup env.v xv = some x) (hv : s.refs[tl]? = some (.varray vs)) (hk : k < vs.length) :
    evaluate s env [.app .aupdate [.var h, .lit (.intLit k), .var xv]] =
      ({ s with refs := s.refs.set tl (.varray (vs.set k x)) }, .val [.conv none []]) := by
  have hargs : evaluate s env [.var xv, .lit (.intLit k), .var h] =
      (s, .val [x, .litv (.intLit k), .loc b tl]) :=
    evaluate_cons_val (s₁ := s) (by simp [evaluate, hx])
      (evaluate_cons_val (s₁ := s) (by simp [evaluate]) (by simp [evaluate, hh]))
  have := evaluate_app_simple (s := s) (s₁ := s) (env := env) (op := .aupdate)
    (args := [.var h, .lit (.intLit k), .var xv]) (vs := [x, .litv (.intLit k), .loc b tl])
    (refs := s.refs.set tl (.varray (vs.set k x))) (ffi := s.ffi) (r := .val (.conv none []))
    (by simpa using hargs) rfl
    (by
      have hneg : ¬ ((k : Int) < 0) := by omega
      have hle : ¬ (vs.length ≤ k) := by omega
      simp [doApp, doAppBasic, doAppNumericCore, storeLookup, hv, updateIndexed, hneg, hle,
        storeAssign, storeValueSameType])
  simpa [listResult] using this

/-- The bucket array: `Array.sub h 0`. -/
abbrev cellArr (h : VarN) : Exp := .app .asub [.var (.short h), .lit (.intLit ((0 : Nat) : Int))]
/-- The size: `Array.sub h 1`. -/
abbrev cellSize (h : VarN) : Exp := .app .asub [.var (.short h), .lit (.intLit ((1 : Nat) : Int))]

/-- In the table's environment, the cell and its bucket array. -/
structure TblAt {K V : Type} (BI : RefInv (Bkt K V)) (st : TRaw K V) (r : Store Value) (tl : Nat)
    (b : Bool) (a : Nat) (bs : List Value) : Prop where
  cell : r[tl]? = some (.varray [.loc b a, .litv (.intLit st.size)])
  ne : a ≠ tl
  arr : r[a]? = some (.varray bs)
  elems : List.Forall₂ BI st.buckets.toList bs

theorem TblAt.rel {K V : Type} {BI : RefInv (Bkt K V)} {st : TRaw K V} {r : Store Value} {tl : Nat}
    {b : Bool} {a : Nat} {bs : List Value} (h : TblAt BI st r tl b a bs) : (tblRel BI tl).rel st r :=
  ⟨b, a, bs, h.cell, h.ne, h.arr, h.elems⟩

theorem tblRel_at {K V : Type} {BI : RefInv (Bkt K V)} {st : TRaw K V} {r : Store Value} {tl : Nat}
    (h : (tblRel BI tl).rel st r) : ∃ b a bs, TblAt BI st r tl b a bs := by
  obtain ⟨b, a, bs, h1, h2, h3, h4⟩ := h
  exact ⟨b, a, bs, ⟨h1, h2, h3, h4⟩⟩

/-! ## The primitives' code -/

section
variable {K V ε : Type} {BI : RefInv (Bkt K V)} {B : RefInv ε} {env : SemEnv Value} {h : VarN}
  {b : Bool} {tl : Nat}

/-- `tSize`: `Array.sub h 1`. -/
theorem EvalM_tSize (hh : nsLookup env.v (.short h) = some (.loc b tl)) :
    EvalM (tblRel BI tl) env (cellSize h) NAT B (tSize (K := K) (V := V)) := by
  intro τ s st hst
  obtain ⟨b', a, bs, ht⟩ := tblRel_at hst
  refine ⟨s.refs, .val [.litv (.intLit st.size)], ⟨s.clock, s.clock, ?_⟩, Frame.refl _ _, hst, _, rfl, rfl⟩
  exact evaluate_asub_lit { s with clock := s.clock } hh ht.cell (k := 1) (by simp)

/-- `tNB`: `let ar = Array.sub h 0 in Array.length ar`. -/
theorem EvalM_tNB {ar : VarN} (hh : nsLookup env.v (.short h) = some (.loc b tl)) :
    EvalM (tblRel BI tl) env (.let_ (some ar) (cellArr h) (.app .alength [.var (.short ar)])) NAT B
      (tNB (K := K) (V := V)) := by
  intro τ s st hst
  obtain ⟨b', a, bs, ht⟩ := tblRel_at hst
  have hlen := forall₂_length ht.elems
  refine ⟨s.refs, .val [.litv (.intLit bs.length)], ⟨s.clock, s.clock, ?_⟩, Frame.refl _ _, hst, _, rfl, ?_⟩
  · rw [evaluate_let_val (evaluate_asub_lit { s with clock := s.clock } hh (by simpa using ht.cell) (k := 0) (by simp))]
    simpa using evaluate_alength (s := { s with clock := s.clock }) (arr := .short ar)
      (env := { env with v := nsOptBind (some ar) (.loc b' a) env.v })
      nsl_self (by simpa using ht.arr)
  · show _ = _
    simp [tNB, ← hlen]

/-- `tGetB i`: `let ix = i in let ar = Array.sub h 0 in if ix < Array.length ar then Array.sub ar ix else nil`. -/
theorem EvalM_tGetB {ix ar : VarN} {ei ed : Exp} {i : Nat}
    (hh : nsLookup env.v (.short h) = some (.loc b tl)) (hne₁ : ix ≠ h) (hne₂ : ar ≠ ix)
    (hi : Eval env ei (NAT i))
    (hd : ∀ v w, Eval { env with v := nsOptBind (some ar) w (nsOptBind (some ix) v env.v) } ed (BI .nil)) :
    EvalM (tblRel BI tl) env
      (.let_ (some ix) ei (.let_ (some ar) (cellArr h)
        (.if_ (ltLen (.short ix) (.short ar)) (.app .asub [.var (.short ar), .var (.short ix)]) ed)))
      BI B (tGetB (K := K) (V := V) i) := by
  refine EvalM_let hi fun v hv => ?_
  have hv' : v = .litv (.intLit i) := hv
  subst hv'
  intro τ s st hst
  obtain ⟨b', a, bs, ht⟩ := tblRel_at hst
  have hh' : nsLookup (nsOptBind (some ix) (.litv (.intLit i)) env.v) (.short h) = some (.loc b tl) :=
    nsl_ne hne₁ hh
  have hcell := evaluate_asub_lit (env := { env with v := nsOptBind (some ix) (.litv (.intLit i)) env.v })
    { s with clock := s.clock } hh' (by simpa using ht.cell) (k := 0) (by simp)
  simp only [List.getElem_cons_zero] at hcell
  let env₂ : SemEnv Value :=
    { env with v := nsOptBind (some ar) (Value.loc b' a) (nsOptBind (some ix) (Value.litv (.intLit i)) env.v) }
  have har : nsLookup env₂.v (.short ar) = some (.loc b' a) := nsl_self
  have hix : nsLookup env₂.v (.short ix) = some (.litv (.intLit i)) :=
    nsl_ne hne₂ nsl_self
  have hlen := forall₂_length ht.elems
  have hsz : st.buckets.size = bs.length := by rw [← Array.length_toList, hlen]
  by_cases hi : i < bs.length
  · have hi' : i < st.buckets.size := by rw [hsz]; exact hi
    refine ⟨s.refs, .val [bs[i]], ⟨s.clock, s.clock, ?_⟩, Frame.refl _ _, hst, bs[i], rfl, ?_⟩
    · rw [evaluate_let_val hcell]
      unfold ltLen; erw [evaluate_if_val (evaluate_ltLen (env := env₂) _ har hix (by simpa using ht.arr))]
      simp only [decide_eq_true hi, if_true]
      exact evaluate_asub _ har hix (by simpa using ht.arr) hi
    · have := forall₂_get ht.elems i (by simpa using hi')
      simpa [tGetB, Array.getD, hi', Array.getElem_toList] using this
  · obtain ⟨w, extra, ⟨ck₁, ck₂, hev⟩, hA⟩ := hd (.litv (.intLit i)) (.loc b' a) τ s
    refine ⟨s.refs ++ extra, .val [w], ⟨ck₁, ck₂, ?_⟩, Frame.append hst _,
      StateRel.rel_append hst _, w, rfl, ?_⟩
    · have hcell' := evaluate_asub_lit (env := { env with v := nsOptBind (some ix) (.litv (.intLit i)) env.v })
        { s with clock := ck₁ } hh' (by simpa using ht.cell) (k := 0) (by simp)
      simp only [List.getElem_cons_zero] at hcell'
      rw [evaluate_let_val hcell']
      unfold ltLen; erw [evaluate_if_val (evaluate_ltLen (env := env₂) _ har hix (by simpa using ht.arr))]
      simp only [decide_eq_false hi, Bool.false_eq_true, if_false]
      exact hev
    · have hi' : ¬ i < st.buckets.size := by rw [hsz]; exact hi
      simpa [tGetB, Array.getD, hi'] using hA

/-- `tSetB i y`: `let ix = i in let xv = y in let ar = Array.sub h 0 in
if ix < Array.length ar then Array.update ar ix xv else ()`. -/
theorem EvalM_tSetB {ix xv ar : VarN} {ei ey : Exp} {i : Nat} {y : Bkt K V}
    (hh : nsLookup env.v (.short h) = some (.loc b tl)) (hne₁ : ix ≠ h) (hne₂ : xv ≠ h)
    (hne₃ : xv ≠ ix) (hne₄ : ar ≠ ix) (hne₅ : ar ≠ xv)
    (hi : Eval env ei (NAT i))
    (hy : ∀ v, Eval { env with v := nsOptBind (some ix) v env.v } ey (BI y)) :
    EvalM (tblRel BI tl) env
      (.let_ (some ix) ei (.let_ (some xv) ey (.let_ (some ar) (cellArr h)
        (.if_ (ltLen (.short ix) (.short ar))
          (.app .aupdate [.var (.short ar), .var (.short ix), .var (.short xv)]) (.con none [])))))
      UNIT B (tSetB (K := K) (V := V) i y) := by
  refine EvalM_let hi fun v hv => ?_
  have hv' : v = .litv (.intLit i) := hv
  subst hv'
  refine EvalM_let (hy _) fun x hx => ?_
  intro τ s st hst
  obtain ⟨b', a, bs, ht⟩ := tblRel_at hst
  let env₁ : SemEnv Value := { env with v := nsOptBind (some xv) x (nsOptBind (some ix) (.litv (.intLit i)) env.v) }
  have hh' : nsLookup env₁.v (.short h) = some (.loc b tl) :=
    nsl_ne hne₂ (nsl_ne hne₁ hh)
  let env₂ : SemEnv Value := { env₁ with v := nsOptBind (some ar) (.loc b' a) env₁.v }
  have har : nsLookup env₂.v (.short ar) = some (.loc b' a) := nsl_self
  have hix : nsLookup env₂.v (.short ix) = some (.litv (.intLit i)) :=
    nsl_ne hne₄ (nsl_ne hne₃ nsl_self)
  have hxv : nsLookup env₂.v (.short xv) = some x :=
    nsl_ne hne₅ nsl_self
  have hcell := evaluate_asub_lit (env := env₁) { s with clock := s.clock } hh' (by simpa using ht.cell)
    (k := 0) (by simp)
  simp only [List.getElem_cons_zero] at hcell
  have hlen := forall₂_length ht.elems
  have hsz : st.buckets.size = bs.length := by rw [← Array.length_toList, hlen]
  have hlt : a < s.refs.length := (List.getElem?_eq_some_iff.mp ht.arr).1
  by_cases hi : i < bs.length
  · have hrel : (tblRel BI tl).rel { st with buckets := st.buckets.setIfInBounds i y }
        (s.refs.set a (.varray (bs.set i x))) := by
      refine ⟨b', a, bs.set i x, ?_, ht.ne, List.getElem?_set_self hlt, ?_⟩
      · rw [List.getElem?_set_ne ht.ne]; exact ht.cell
      · simpa [Array.toList_setIfInBounds] using forall₂_set hx ht.elems i
    refine ⟨s.refs.set a (.varray (bs.set i x)), .val [.conv none []], ⟨s.clock, s.clock, ?_⟩,
      ⟨by simp, fun l _ hn => ?_, fun l _ ho => ?_⟩, hrel, _, rfl, rfl⟩
    · rw [evaluate_let_val hcell]
      unfold ltLen; erw [evaluate_if_val (evaluate_ltLen (env := env₂) _ har hix (by simpa using ht.arr))]
      simp only [decide_eq_true hi, if_true]
      simpa using evaluate_aupdate { s with clock := s.clock } har hix hxv (by simpa using ht.arr) hi
    · refine List.getElem?_set_ne (fun he => hn (Or.inr ⟨b', st.size, ?_⟩))
      rw [← he]; exact ht.cell
    · rcases ho with rfl | ⟨b₂, n₂, hc⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨b₂, n₂, ?_⟩
        rwa [List.getElem?_set_ne ht.ne] at hc
  · have hi' : ¬ i < st.buckets.size := by rw [hsz]; exact hi
    have hrel : (tblRel BI tl).rel { st with buckets := st.buckets.setIfInBounds i y } s.refs :=
      ⟨b', a, bs, ht.cell, ht.ne, ht.arr, by simpa [Array.setIfInBounds, hi'] using ht.elems⟩
    refine ⟨s.refs, .val [.conv none []], ⟨s.clock, s.clock, ?_⟩, Frame.refl _ _, hrel, _, rfl, rfl⟩
    rw [evaluate_let_val hcell]
    unfold ltLen; erw [evaluate_if_val (evaluate_ltLen (env := env₂) _ har hix (by simpa using ht.arr))]
    simp only [decide_eq_false hi, Bool.false_eq_true, if_false]
    rw [Flapjack.EvaluateHOL.evaluate]
    simp [doConCheck, buildConv, Flapjack.EvaluateHOL.evaluate]

/-- `tSetSize n`: `let nv = n in Array.update h 1 nv`. -/
theorem EvalM_tSetSize {nv : VarN} {en : Exp} {n : Nat}
    (hh : nsLookup env.v (.short h) = some (.loc b tl)) (hne : nv ≠ h) (hn : Eval env en (NAT n)) :
    EvalM (tblRel BI tl) env
      (.let_ (some nv) en (.app .aupdate [.var (.short h), .lit (.intLit ((1 : Nat) : Int)), .var (.short nv)]))
      UNIT B (tSetSize (K := K) (V := V) n) := by
  refine EvalM_let hn fun v hv => ?_
  have hv' : v = .litv (.intLit n) := hv
  subst hv'
  intro τ s st hst
  obtain ⟨b', a, bs, ht⟩ := tblRel_at hst
  have hh' := nsl_ne (v := .litv (.intLit n)) hne hh
  have hlt : tl < s.refs.length := (List.getElem?_eq_some_iff.mp ht.cell).1
  have hupd := evaluate_aupdate_lit (env := { env with v := nsOptBind (some nv) (.litv (.intLit n)) env.v })
    { s with clock := s.clock } hh' nsl_self (by simpa using ht.cell) (k := 1) (by simp)
  have hrel : (tblRel BI tl).rel { st with size := n }
      (s.refs.set tl (.varray ([Value.loc b' a, .litv (.intLit st.size)].set 1 (.litv (.intLit n))))) := by
    refine ⟨b', a, bs, by simp [List.getElem?_set_self hlt], ht.ne, ?_, ht.elems⟩
    rw [List.getElem?_set_ne (Ne.symm ht.ne)]; exact ht.arr
  refine ⟨_, .val [.conv none []], ⟨s.clock, s.clock, by simpa using hupd⟩,
    ⟨by simp, fun l _ hn => List.getElem?_set_ne (fun he => hn (Or.inl he.symm)), fun l _ ho => ?_⟩,
    hrel, _, rfl, rfl⟩
  rcases ho with rfl | ⟨b₂, n₂, hc⟩
  · exact Or.inl rfl
  · simp [List.getElem?_set_self hlt] at hc
    have hl : l = a := by omega
    subst hl
    exact Or.inr ⟨b', st.size, ht.cell⟩

/-- `tRealloc n`: `let nv = n in let xv = nil in let na = Array.array nv xv in Array.update h 0 na`. -/
theorem EvalM_tRealloc {nv xv na : VarN} {en ex : Exp} {n : Nat}
    (hh : nsLookup env.v (.short h) = some (.loc b tl)) (hne₁ : nv ≠ h) (hne₂ : xv ≠ h) (hne₃ : xv ≠ nv)
    (hne₄ : na ≠ h) (hn : Eval env en (NAT n))
    (hx : ∀ v, Eval { env with v := nsOptBind (some nv) v env.v } ex (BI .nil)) :
    EvalM (tblRel BI tl) env
      (.let_ (some nv) en (.let_ (some xv) ex (.let_ (some na)
        (.app .aalloc [.var (.short nv), .var (.short xv)])
        (.app .aupdate [.var (.short h), .lit (.intLit ((0 : Nat) : Int)), .var (.short na)]))))
      UNIT B (tRealloc (K := K) (V := V) n) := by
  refine EvalM_let hn fun v hv => ?_
  have hv' : v = .litv (.intLit n) := hv
  subst hv'
  refine EvalM_let (hx _) fun x hxv => ?_
  intro τ s st hst
  obtain ⟨b', a, bs, ht⟩ := tblRel_at hst
  let env₁ : SemEnv Value := { env with v := nsOptBind (some xv) x (nsOptBind (some nv) (.litv (.intLit n)) env.v) }
  have hnv : nsLookup env₁.v (.short nv) = some (.litv (.intLit n)) :=
    nsl_ne hne₃ nsl_self
  have hxl : nsLookup env₁.v (.short xv) = some x := nsl_self
  have hh₁ : nsLookup env₁.v (.short h) = some (.loc b tl) :=
    nsl_ne hne₂ (nsl_ne hne₁ hh)
  have hargs : Runs s env₁ [.var (.short xv), .var (.short nv)] s (.val [x, .litv (.intLit n)]) :=
    ⟨0, 0, evaluate_cons_val (s₁ := { s with clock := 0 }) (by simp [evaluate, hxl]) (by simp [evaluate, hnv])⟩
  have halloc := Runs.aalloc hargs
  let r₁ := s.refs ++ [.varray (List.replicate n x)]
  let env₂ : SemEnv Value := { env₁ with v := nsOptBind (some na) (.loc true s.refs.length) env₁.v }
  have hh₂ : nsLookup env₂.v (.short h) = some (.loc b tl) := nsl_ne hne₄ hh₁
  have hnal : nsLookup env₂.v (.short na) = some (.loc true s.refs.length) := nsl_self
  have htl : tl < s.refs.length := (List.getElem?_eq_some_iff.mp ht.cell).1
  have hcell₁ : r₁[tl]? = some (.varray [.loc b' a, .litv (.intLit st.size)]) := by
    simp [r₁, List.getElem?_append_left htl, ht.cell]
  have hupd := evaluate_aupdate_lit (env := env₂) { s with clock := 0, refs := r₁ } hh₂ hnal
    (by simpa using hcell₁) (k := 0) (by simp)
  let r₂ := r₁.set tl (.varray ([Value.loc b' a, .litv (.intLit st.size)].set 0 (.loc true s.refs.length)))
  have hne : s.refs.length ≠ tl := by omega
  have hrel : (tblRel BI tl).rel { st with buckets := Array.replicate n .nil } r₂ := by
    refine ⟨true, s.refs.length, List.replicate n x, ?_, hne, ?_, ?_⟩
    · have : tl < r₁.length := by simp only [r₁, List.length_append, List.length_singleton]; omega
      simp [r₂, List.getElem?_set_self this]
    · rw [List.getElem?_set_ne (Ne.symm hne)]; simp [r₁]
    · simpa using forall₂_replicate hxv n
  refine ⟨r₂, .val [.conv none []], ?_, ⟨by simp [r₂, r₁], fun l hl hn => ?_, fun l hl ho => ?_⟩,
    hrel, _, rfl, rfl⟩
  · have hu : Runs { s with refs := r₁ } env₂
        [.app .aupdate [.var (.short h), .lit (.intLit ((0 : Nat) : Int)), .var (.short na)]] { s with refs := r₂ }
        (.val [.conv none []]) := ⟨0, 0, by simpa [r₂] using hupd⟩
    have := Runs.let_ (n := some na) halloc hu (by simp)
    simpa [r₁, env₂] using this
  · have : l ≠ tl := fun he => hn (Or.inl he)
    simp [r₂, r₁, List.getElem?_set_ne (Ne.symm this), List.getElem?_append_left hl]
  · rcases ho with rfl | ⟨b₂, n₂, hc⟩
    · exact Or.inl rfl
    · have : tl < r₁.length := by simp only [r₁, List.length_append, List.length_singleton]; omega
      simp [r₂, List.getElem?_set_self this] at hc
      omega

end

end ConPastel.Translator
