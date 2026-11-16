import ConPastel.Program.Assemble
import ConPastel.Program.Scale

/-!
# Programs as a sequence of recursive groups

CakeML's compiler gives every closure of a `Dletrec` group access to the
whole group, so one group of thousands of functions compiles in hours. The
units are therefore declared as a sequence of smaller groups `g₀, g₁, …`
(each closed under mutual recursion, every dependency in the same or an
earlier group), followed by the main declarations.

The variable environment stays one flat binding list: group `k` runs in
`flatEnv c Lₖ` and adds `groupBinds gₖ (flatEnv c Lₖ)` in front of `Lₖ`.
Lookups of earlier units follow from membership and one distinctness fact
about the final list. That fact is checked on character codes after a
merge sort (`msortF`), since the group order is not alphabetical.
-/

namespace ConPastel.Program
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString ConPastel.Translator ConPastel.Main

/-! ## Distinctness via merge sort -/

/-- Merge (fuel: the total length is enough). -/
def mergeF : Nat → List (List Nat) → List (List Nat) → List (List Nat)
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | n + 1, x :: xs, y :: ys =>
    if lexLtN x y then x :: mergeF n xs (y :: ys) else y :: mergeF n (x :: xs) ys

theorem mergeF_perm : ∀ (n : Nat) (xs ys : List (List Nat)), (mergeF n xs ys).Perm (xs ++ ys)
  | 0, xs, ys => by simp [mergeF]
  | _ + 1, [], ys => by simp [mergeF]
  | _ + 1, x :: xs, [] => by simp [mergeF]
  | n + 1, x :: xs, y :: ys => by
    unfold mergeF
    split
    · exact (mergeF_perm n xs (y :: ys)).cons x
    · have h := (mergeF_perm n (x :: xs) ys).cons y
      refine h.trans ?_
      exact (List.perm_middle (a := y) (l₁ := x :: xs) (l₂ := ys)).symm

/-- Merge sort (fuel: the recursion depth). -/
def msortF : Nat → List (List Nat) → List (List Nat)
  | 0, l => l
  | n + 1, l =>
    if l.length ≤ 1 then l
    else mergeF l.length (msortF n (l.take (l.length / 2))) (msortF n (l.drop (l.length / 2)))

theorem msortF_perm : ∀ (n : Nat) (l : List (List Nat)), (msortF n l).Perm l
  | 0, l => by simp [msortF]
  | n + 1, l => by
    unfold msortF
    split
    · exact List.Perm.refl l
    · refine (mergeF_perm _ _ _).trans ?_
      have h := (msortF_perm n (l.take (l.length / 2))).append (msortF_perm n (l.drop (l.length / 2)))
      rw [List.take_append_drop] at h
      exact h

theorem nodup_names_msort (xs : List MlString) (names : List (List Char)) (fuel : Nat)
    (h1 : xs = names.map fun cs => ofString (String.ofList cs))
    (h2 : sortedN (msortF fuel (names.map charKey)) = true) : xs.Nodup :=
  nodup_names_of_keys xs names h1 ((msortF_perm fuel _).nodup_iff.mp (nodup_of_sortedN _ h2))

/-! ## Flat environments and groups -/

abbrev Fn := VarN × VarN × Exp

/-- An environment whose variables are one flat binding list. -/
def flatEnv (c : Namespace ModN ConN (Nat × Stamp)) (L : List (VarN × Value)) : SemEnv Value :=
  { v := .bind L [], c := c }

/-- The bindings a group adds. -/
def groupBinds (g : List Fn) (E : SemEnv Value) : List (VarN × Value) :=
  g.map fun (n, _, _) => (n, .recclosure E g n)

theorem foldr_flat (G : List Fn) (E : SemEnv Value) (L : List (VarN × Value)) :
    ∀ l : List Fn, l.foldr (fun (name, _, _) rest => nsBind name (Value.recclosure E G name) rest)
        (Namespace.bind L [] : Namespace ModN VarN Value) =
      .bind (l.map (fun (n, _, _) => (n, Value.recclosure E G n)) ++ L) []
  | [] => rfl
  | (a, b, e) :: l => by rw [List.foldr_cons, foldr_flat G E L l]; rfl

theorem buildRecEnv_flat (g : List Fn) (E : SemEnv Value) (L : List (VarN × Value)) :
    buildRecEnv g E (.bind L []) = .bind (groupBinds g E ++ L) [] :=
  foldr_flat g E L g

theorem mem_groupBinds {g : List Fn} (E : SemEnv Value) {n x : VarN} {b : Exp} (h : (n, x, b) ∈ g) :
    (n, Value.recclosure E g n) ∈ groupBinds g E :=
  List.mem_map.mpr ⟨(n, x, b), h, rfl⟩

theorem keys_groupBinds (g : List Fn) (E : SemEnv Value) :
    (groupBinds g E).map Prod.fst = g.map fun p => p.1 := by
  simp [groupBinds, List.map_map, Function.comp_def]

/-- A group's names are distinct when the list it extends is. -/
theorem nodup_group_of {g : List Fn} {E : SemEnv Value} {L : List (VarN × Value)}
    (h : ((groupBinds g E ++ L).map Prod.fst).Nodup) : (g.map fun p => p.1).Nodup := by
  rw [List.map_append, keys_groupBinds] at h
  exact (List.nodup_append.mp h).1

/-- The list a group extends is distinct when the extended one is. -/
theorem nodup_rest_of {g : List Fn} {E : SemEnv Value} {L : List (VarN × Value)}
    (h : ((groupBinds g E ++ L).map Prod.fst).Nodup) : (L.map Prod.fst).Nodup := by
  rw [List.map_append] at h
  exact (List.nodup_append.mp h).2.1

/-- A lookup in a flat binding list. -/
theorem lookup_flat {L : List (VarN × Value)} {n : VarN} {v : Value}
    (hnd : (L.map Prod.fst).Nodup) (hm : (n, v) ∈ L) :
    nsLookup (Namespace.bind L [] : Namespace ModN VarN Value) (.short n) = some v := by
  rw [nsLookup_bind_short]; exact lookup_of_mem_nodup hnd hm

/-- A unit of an earlier group, seen from group `g` (a certificate's
dependency hypothesis). -/
theorem depLookup (c : Namespace ModN ConN (Nat × Stamp)) (g : List Fn) (L : List (VarN × Value))
    {n : VarN} {v : Value} (hnd : ((groupBinds g (flatEnv c L) ++ L).map Prod.fst).Nodup)
    (hm : (n, v) ∈ L) :
    nsLookup (buildRecEnv g (flatEnv c L) (flatEnv c L).v) (.short n) = some v := by
  show nsLookup (buildRecEnv g (flatEnv c L) (.bind L [])) (.short n) = some v
  rw [buildRecEnv_flat]
  exact lookup_flat hnd (List.mem_append_right _ hm)

/-! ## Running the groups -/

/-- The bindings after the groups `gs`, starting from `L`. -/
def bindsAfter (c : Namespace ModN ConN (Nat × Stamp)) : List (List Fn) → List (VarN × Value) →
    List (VarN × Value)
  | [], L => L
  | g :: gs, L => bindsAfter c gs (groupBinds g (flatEnv c L) ++ L)

/-- Each group's names are distinct and its constructors well-formed. -/
def GroupsOk (c : Namespace ModN ConN (Nat × Stamp)) : List (List Fn) → Prop
  | [] => True
  | g :: gs => ((g.map fun (f, _, _) => f).Nodup ∧
      g.all (fun (_, _, e) => everyExp (oneConCheck c) e) = true) ∧ GroupsOk c gs

theorem GroupsOk.nil (c : Namespace ModN ConN (Nat × Stamp)) : GroupsOk c [] := trivial

theorem GroupsOk.cons (c : Namespace ModN ConN (Nat × Stamp)) (g : List Fn) (gs : List (List Fn))
    (h1 : (g.map fun p => p.1).Nodup) (h2 : g.all (fun (_, _, e) => everyExp (oneConCheck c) e) = true)
    (h3 : GroupsOk c gs) : GroupsOk c (g :: gs) := ⟨⟨h1, h2⟩, h3⟩

theorem extend_flat (c : Namespace ModN ConN (Nat × Stamp)) (g : List Fn) (L : List (VarN × Value)) :
    extendDecEnv { v := buildRecEnv g (flatEnv c L) nsEmpty, c := nsEmpty } (flatEnv c L) =
      flatEnv c (groupBinds g (flatEnv c L) ++ L) := by
  have h := buildRecEnv_flat g (flatEnv c L) []
  simp only [List.append_nil] at h
  have hn : (nsEmpty : Namespace ModN VarN Value) = .bind [] [] := rfl
  simp only [extendDecEnv, hn, h, nsAppend_nsEmpty]
  simp [flatEnv, nsAppend]

theorem groups_run {σ : Type} (c : Namespace ModN ConN (Nat × Stamp)) (loc : Flapjack.Misc.Location.Locs) :
    ∀ (gs : List (List Fn)) (L : List (VarN × Value)) (d : Dec) (ds : List Dec) (s s' : State σ)
      (envR : SemEnv Value), GroupsOk c gs →
      DeclsRun s (flatEnv c (bindsAfter c gs L)) (d :: ds) s' envR →
      ∃ env', DeclsRun s (flatEnv c L) (gs.map (Dec.dletrec loc) ++ d :: ds) s' env'
  | [], _, _, _, _, _, envR, _, h => ⟨envR, h⟩
  | g :: gs, L, d, ds, s, s', envR, hok, h => by
    obtain ⟨⟨hnd, hcon⟩, hok⟩ := hok
    have h₁ := DeclsRun.dletrec (loc := loc) (env := flatEnv c L) s hnd hcon
    obtain ⟨env', h₂⟩ := groups_run c loc gs _ d ds s s' envR hok h
    rw [← extend_flat] at h₂
    cases gs with
    | nil => exact ⟨_, DeclsRun.cons h₁ h₂⟩
    | cons g' gs' => exact ⟨_, DeclsRun.cons h₁ h₂⟩

/-- The environment after the datatypes is flat and empty. -/
theorem dtEnv_flat (tds : TypeDef) : dtEnv tds = flatEnv (dtEnv tds).c [] := by
  simp [dtEnv, flatEnv, extendDecEnv, nsEmpty, nsAppend, ConPastel.initEnv]

/-- **Whole-program correctness with groups**: `Dtype tds`, the groups `gs`,
then the main program. -/
theorem program_completes_groups (tds : TypeDef) (gs : List (List Fn)) (Lm : List (VarN × Value))
    (hLm : bindsAfter (dtEnv tds).c gs [] = Lm)
    (entryName revName : String) (entry : List Nat → Bool)
    (hdup : tds.all checkDupCtors = true)
    (hok : GroupsOk (dtEnv tds).c gs)
    (ve vr : Value)
    (hentry : nsLookup (Namespace.bind Lm [] : Namespace ModN VarN Value) (.short (ofString entryName)) = some ve)
    (he : Arrow (LIST NAT) BOOL entry ve)
    (hrev : nsLookup (Namespace.bind Lm [] : Namespace ModN VarN Value) (.short (ofString revName)) = some vr)
    (hr : Arrow (PAIR (LIST NAT) (LIST NAT)) (LIST NAT) revAppT vr)
    (hlist : HasListCons (dtEnv tds).c)
    (hn₁ : ofString entryName ≠ ofString bufName) (hn₂ : ofString entryName ≠ ofString readAllName)
    (hn₃ : ofString revName ≠ ofString bufName) (hn₄ : ofString revName ≠ ofString readAllName)
    (input : ByteArray) :
    ∃ events, Completes (ConPastel.initState (initFfi input)) ConPastel.initEnv
        (.dtype Flapjack.Misc.Location.unknownLoc tds ::
          (gs.map (Dec.dletrec Flapjack.Misc.Location.unknownLoc) ++ mainDecs entryName revName)) events ∧
      writtenBytes events = verdictBytes (entry (input.toList.map UInt8.toNat)) := by
  let s : State Stdio := ConPastel.initState (initFfi input)
  have hdt := DeclsRun.dtype (loc := Flapjack.Misc.Location.unknownLoc) (env := ConPastel.initEnv) s hdup
  let s₁ : State Stdio := { s with nextTypeStamp := s.nextTypeStamp + tds.length }
  let c := (dtEnv tds).c
  obtain ⟨s', envM, reads, cc, dd, hrun, hevents, hreads⟩ :=
    mainRun entryName revName entry (flatEnv c Lm) ve vr hentry he hrev hr hlist
      hn₁ hn₂ hn₃ hn₄ s₁ rfl (input.toList.map (·.toBitVec)) rfl
  rw [← hLm] at hrun
  have hmain : mainDecs entryName revName = _ :: _ := rfl
  rw [hmain] at hrun
  obtain ⟨env', hgs⟩ := groups_run c Flapjack.Misc.Location.unknownLoc gs [] _ _ s₁ s' envM hok hrun
  rw [← hmain, ← dtEnv_flat] at hgs
  have hgs' : DeclsRun s₁ (extendDecEnv { v := nsEmpty, c := buildTdefs s.nextTypeStamp tds } ConPastel.initEnv)
      (gs.map (Dec.dletrec Flapjack.Misc.Location.unknownLoc) ++ mainDecs entryName revName) s' env' := hgs
  rw [hmain] at hgs'
  obtain ⟨ck₁, ck₂, heval⟩ : DeclsRun s ConPastel.initEnv
      (.dtype Flapjack.Misc.Location.unknownLoc tds ::
        (gs.map (Dec.dletrec Flapjack.Misc.Location.unknownLoc) ++ mainDecs entryName revName)) s'
      (extendDecEnv env' { v := nsEmpty, c := buildTdefs s.nextTypeStamp tds }) := by
    rw [hmain]
    cases hl : gs.map (Dec.dletrec Flapjack.Misc.Location.unknownLoc) with
    | nil => rw [hl] at hgs'; exact DeclsRun.cons hdt hgs'
    | cons d ds => rw [hl] at hgs'; exact DeclsRun.cons hdt hgs'
  refine ⟨s'.ffi.ioEvents, ⟨ck₁, s'.ffi,
    .val (extendDecEnv env' { v := nsEmpty, c := buildTdefs s.nextTypeStamp tds }),
    ?_, by simp, by simp, by simp, rfl⟩, ?_⟩
  · simp only [SemanticsHOL.evaluateProgWithClock, Prod.mk.injEq]
    exact ⟨congrArg (fun p => p.1.ffi) heval, congrArg Prod.snd heval⟩
  · have hr' : writtenBytes reads = [] := by simpa [writtenBytes] using writtenBytes_append_reads [] reads hreads
    have h0 : s₁.ffi.ioEvents = [] := rfl
    rw [hevents, h0, List.nil_append, writtenBytes_append, hr', List.nil_append,
      writtenBytes_singleton_write, byteNats_input]

end ConPastel.Program
