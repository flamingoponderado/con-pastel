import ConPastel.Par.Run
import Flapjack.SemanticsProps.Determinism

/-!
# One process of the parallel program, whole

`ParProcess prog`: for every script of FFI answers `io` (`ConPastel.Par.Spec`), the program, run from
CakeML's primitive environment with the FFI oracle `parOracle` at `io`, has exactly one behaviour: it
terminates (normally, or by an FFI call ending the run), and its events satisfy `ProcOk io`.

`par_program_end` proves it for the datatypes, the groups of translated units, and the parallel
main declarations, from the units' certificates; `cake_program_par` instantiates it.
-/

namespace ConPastel.Par
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.SemanticsHOL
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString ConPastel.Translator ConPastel.Program
open ConPastel.Main

/-- **One process of a parallel program is correct**: for every script of FFI answers, its only
behaviour terminates with events satisfying `ProcOk`. -/
def ParProcess (prog : List Dec) : Prop :=
  ∀ io : ParIO, ∃ st env, PrimTypesHOL.primSemEnv (initParFfi io) = some (st, env) ∧
    ∃ outcome events, semanticsProg st env prog (.terminate outcome events) ∧ ProcOk io events ∧
      ∀ b, semanticsProg st env prog b → b = .terminate outcome events

/-- **The per-process theorem for an assembled parallel program.** -/
theorem par_program_end (tds : TypeDef) (gs : List (List Fn)) (Lm : List (VarN × Value))
    (hLm : bindsAfter (dtEnv tds).c gs [] = Lm)
    (p1N okN jcN vN revN : String)
    (hdup : tds.all checkDupCtors = true)
    (hok : GroupsOk (dtEnv tds).c gs)
    (INVp : RefInv Phase1) (v1 vok vjc vv vr : Value)
    (h1 : nsLookup (Namespace.bind Lm [] : Namespace ModN VarN Value) (.short (ofString p1N)) = some v1)
    (c1 : Arrow (LIST NAT) INVp phase1 v1)
    (hokL : nsLookup (Namespace.bind Lm [] : Namespace ModN VarN Value) (.short (ofString okN)) = some vok)
    (cok : Arrow INVp BOOL phase1Ok vok)
    (hjc : nsLookup (Namespace.bind Lm [] : Namespace ModN VarN Value) (.short (ofString jcN)) = some vjc)
    (cjc : Arrow INVp (Arrow (LIST NAT) NAT) jobCode vjc)
    (hvd : nsLookup (Namespace.bind Lm [] : Namespace ModN VarN Value) (.short (ofString vN)) = some vv)
    (cvd : Arrow INVp (Arrow (LIST NAT) NAT) verdictCode vv)
    (hrev : nsLookup (Namespace.bind Lm [] : Namespace ModN VarN Value) (.short (ofString revN)) = some vr)
    (crev : Arrow (PAIR (LIST NAT) (LIST NAT)) (LIST NAT) revAppT vr)
    (hlist : HasListCons (dtEnv tds).c)
    (hfresh : ∀ n ∈ [p1N, okN, jcN, vN, revN], ∀ m ∈ mainNames, ofString n ≠ ofString m) :
    ParProcess (.dtype Flapjack.Misc.Location.unknownLoc tds ::
      (gs.map (Dec.dletrec Flapjack.Misc.Location.unknownLoc) ++ parMainDecs p1N okN jcN vN revN)) := by
  intro io
  let s : State ParIO := ConPastel.initState (initParFfi io)
  refine ⟨s, ConPastel.initEnv, primSemEnv_eq _, ?_⟩
  have hdt := DeclsRun.dtype (loc := Flapjack.Misc.Location.unknownLoc) (env := ConPastel.initEnv) s hdup
  let s₁ : State ParIO := { s with nextTypeStamp := s.nextTypeStamp + tds.length }
  let c := (dtEnv tds).c
  obtain ⟨s', r, evs, hD, hr, hevs, hproc⟩ :=
    parMainRun (INVp := INVp) p1N okN jcN vN revN (flatEnv c Lm) v1 vok vjc vv vr h1 c1 hokL cok hjc cjc
      hvd cvd hrev crev hlist hfresh s₁ rfl
  rw [← hLm] at hD
  have hmain : parMainDecs p1N okN jcN vN revN = _ :: _ := rfl
  rw [hmain] at hD
  obtain ⟨r', hG, hr', -⟩ := groups_end c Flapjack.Misc.Location.unknownLoc gs [] _ _ s₁ s' r hok hr hD
  rw [← hmain, ← dtEnv_flat] at hG
  have hG' : DeclsEnd s₁ (extendDecEnv { v := nsEmpty, c := buildTdefs s.nextTypeStamp tds } ConPastel.initEnv)
      (gs.map (Dec.dletrec Flapjack.Misc.Location.unknownLoc) ++ parMainDecs p1N okN jcN vN revN) s' r' := hG
  have hall : DeclsEnd s ConPastel.initEnv (.dtype Flapjack.Misc.Location.unknownLoc tds ::
      (gs.map (Dec.dletrec Flapjack.Misc.Location.unknownLoc) ++ parMainDecs p1N okN jcN vN revN)) s'
      (combineDecResult { v := nsEmpty, c := buildTdefs s.nextTypeStamp tds } r') := by
    rw [hmain] at hG' ⊢
    cases hl : gs.map (Dec.dletrec Flapjack.Misc.Location.unknownLoc) with
    | nil => rw [hl] at hG'; exact DeclsEnd.cons hdt hG' hr'
    | cons d ds => rw [hl] at hG'; exact DeclsEnd.cons hdt hG' hr'
  have hsem := program_end hall (hr'.combine _) rfl
  refine ⟨_, _, hsem, ?_, fun b hb =>
    SemanticsProps.semanticsProg_deterministic s ConPastel.initEnv _ b _ ⟨hb, hsem⟩⟩
  have h0 : s₁.ffi.ioEvents = [] := rfl
  rw [hevs, h0, List.nil_append]
  exact hproc

end ConPastel.Par
