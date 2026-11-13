import ConPastel.Main.Proof
import ConPastel.Semantics.Behaviour
import ConPastel.Semantics.Init

/-!
# Whole programs

A program is the single recursive group of translated units followed by the
main declarations. If the group binds `entry` and `revApp` to closures with
their certificates, the program completes on every input, writing `entry`'s
verdict on the input bytes.
-/

namespace ConPastel.Program
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString ConPastel.Translator ConPastel.Main

/-- Looking up a group member right after the `Dletrec`. -/
theorem lookup_group (funs : List (VarN × VarN × Exp)) (E : SemEnv Value) (n : VarN)
    (hn : n ∈ funs.map (·.1)) :
    nsLookup (extendDecEnv { v := buildRecEnv funs E nsEmpty, c := nsEmpty } E).v (.short n) =
      some (.recclosure E funs n) := by
  obtain ⟨⟨vs, ms⟩, c⟩ := E
  simp only [extendDecEnv]
  have h := nsLookup_buildRecEnv (envC := { v := .bind vs ms, c := c }) (e := nsEmpty) hn
  generalize hb : buildRecEnv funs { v := .bind vs ms, c := c } nsEmpty = b at h
  obtain ⟨bvs, bms⟩ := b
  have hbms : bms = [] := by
    have : ∀ fs : List (VarN × VarN × Exp),
        (fs.foldr (fun (name, _, _) rest => nsBind name (Value.recclosure { v := .bind vs ms, c := c } funs name) rest)
          (nsEmpty : Namespace ModN VarN Value)) = .bind (fs.map fun (name, _, _) =>
            (name, Value.recclosure { v := .bind vs ms, c := c } funs name)) [] := by
      intro fs; induction fs with
      | nil => rfl
      | cons p fs ih => obtain ⟨a, b, e⟩ := p; simp [ih]
    rw [buildRecEnv, this] at hb
    cases hb; rfl
  subst hbms
  simp only [nsAppend, nsLookup_bind_short] at h ⊢
  rw [List.lookup_append, h]
  rfl

theorem writtenBytes_singleton_write (b : Bool) (c d : BitVec 8) :
    writtenBytes [writeEvent b c d] = verdictBytes b := by
  simp [writtenBytes, writeEvent]

theorem writtenBytes_append (a b : List HolIoEvent) :
    writtenBytes (a ++ b) = writtenBytes a ++ writtenBytes b := by
  simp [writtenBytes]

theorem byteNats_input (input : ByteArray) :
    byteNats (input.toList.map (·.toBitVec)) = input.toList.map UInt8.toNat := by
  simp [byteNats, Function.comp_def]

/-- **Whole-program correctness**, generic in the checker `entry`. -/
theorem program_completes (funs : List (VarN × VarN × Exp)) (entryName revName : String)
    (entry : List Nat → Bool)
    (hnodup : (funs.map fun (f, _, _) => f).Nodup)
    (hcon : funs.all (fun (_, _, e) => everyExp (oneConCheck ConPastel.initEnv.c) e) = true)
    (hmemE : ofString entryName ∈ funs.map (·.1)) (hmemR : ofString revName ∈ funs.map (·.1))
    (he : Arrow (LIST NAT) BOOL entry (.recclosure ConPastel.initEnv funs (ofString entryName)))
    (hr : Arrow (PAIR (LIST NAT) (LIST NAT)) (LIST NAT) revApp.cake_tupled
      (.recclosure ConPastel.initEnv funs (ofString revName)))
    (hn₁ : ofString entryName ≠ ofString bufName) (hn₂ : ofString entryName ≠ ofString readAllName)
    (hn₃ : ofString revName ≠ ofString bufName) (hn₄ : ofString revName ≠ ofString readAllName)
    (input : ByteArray) :
    ∃ events, Completes (ConPastel.initState (initFfi input)) ConPastel.initEnv
        (.dletrec Flapjack.Misc.Location.unknownLoc funs :: mainDecs entryName revName) events ∧
      writtenBytes events = verdictBytes (entry (input.toList.map UInt8.toNat)) := by
  let s : State Stdio := ConPastel.initState (initFfi input)
  have hd₁ := DeclsRun.dletrec (loc := Flapjack.Misc.Location.unknownLoc) s hnodup hcon
  let E := extendDecEnv { v := buildRecEnv funs ConPastel.initEnv nsEmpty, c := nsEmpty } ConPastel.initEnv
  have hentry := lookup_group funs ConPastel.initEnv _ hmemE
  have hrev := lookup_group funs ConPastel.initEnv _ hmemR
  have hlist : HasListCons E.c := by
    have : E.c = ConPastel.initEnv.c := by simp [E, extendDecEnv, nsAppend, nsEmpty, ConPastel.initEnv]
    rw [this]; exact initEnv_hasListCons
  obtain ⟨s', envM, reads, c, d, hrun, hevents, hreads⟩ :=
    mainRun entryName revName entry E _ _ hentry he hrev hr hlist hn₁ hn₂ hn₃ hn₄ s rfl
      (input.toList.map (·.toBitVec)) rfl
  obtain ⟨ck₁, ck₂, heval⟩ := DeclsRun.cons hd₁ hrun
  refine ⟨s'.ffi.ioEvents, ⟨ck₁, s'.ffi,
    .val (extendDecEnv envM { v := buildRecEnv funs ConPastel.initEnv nsEmpty, c := nsEmpty }),
    ?_, by simp, by simp, by simp, rfl⟩, ?_⟩
  · simp only [SemanticsHOL.evaluateProgWithClock, Prod.mk.injEq]
    exact ⟨congrArg (fun p => p.1.ffi) heval, congrArg Prod.snd heval⟩
  · have hr' : writtenBytes reads = [] := by simpa [writtenBytes] using writtenBytes_append_reads [] reads hreads
    have h0 : s.ffi.ioEvents = [] := rfl
    rw [hevents, h0, List.nil_append, writtenBytes_append, hr', List.nil_append,
      writtenBytes_singleton_write, byteNats_input]

end ConPastel.Program
