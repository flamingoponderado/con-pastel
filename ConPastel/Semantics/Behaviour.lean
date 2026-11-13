import ConPastel.Spec
import Flapjack.SemanticsProps.Determinism
import ConPastel.Semantics.Init

/-!
# From one completed evaluation to `Implements`

`semanticsProg` is deterministic (flapjack's `semanticsProg_deterministic`), so
proving `Implements prog` comes down to one clock at which the program
completes without a timeout, a type error or an FFI failure, and writes the
expected bytes.
-/

namespace ConPastel
open Flapjack Flapjack.AstHOL Flapjack.SemanticsHOL Flapjack.SemanticPrimitivesHOL

/-- A completed run: some clock at which the program finishes without a
timeout, a type error or an FFI failure. A top-level uncaught exception still
counts, as in CakeML's `semantics_prog`. -/
def Completes {σ : Type} (st : State σ) (env : SemEnv Value) (prog : List Dec)
    (events : List HolIoEvent) : Prop :=
  ∃ k ffi result, evaluateProgWithClock st env k prog = (ffi, result) ∧
    result ≠ .err (.abort .timeoutError) ∧ result ≠ .err (.abort .typeError) ∧
    (∀ e, result ≠ .err (.abort (.ffiError e))) ∧ events = ffi.ioEvents

theorem Completes.terminate {σ : Type} {st : State σ} {env : SemEnv Value} {prog : List Dec}
    {events : List HolIoEvent} (h : Completes st env prog events) :
    semanticsProg st env prog (.terminate .success events) := by
  obtain ⟨k, ffi, result, heval, hto, hty, hffi, hev⟩ := h
  refine ⟨k, ffi, result, heval, ?_, hev, hty⟩
  cases result with
  | val v => exact ⟨hto, rfl⟩
  | err e =>
    cases e with
    | raise v => exact ⟨hto, rfl⟩
    | abort a =>
      cases a with
      | typeError => exact absurd rfl hty
      | timeoutError => exact absurd rfl hto
      | ffiError ev => exact absurd rfl (hffi ev)

/-- The only behaviour of a program that completes. -/
theorem Completes.unique {σ : Type} {st : State σ} {env : SemEnv Value} {prog : List Dec}
    {events : List HolIoEvent} (h : Completes st env prog events) (b : HolBehaviour)
    (hb : semanticsProg st env prog b) : b = .terminate .success events :=
  SemanticsProps.semanticsProg_deterministic st env prog b _ ⟨hb, h.terminate⟩

/-- `ImplementsRef` from a completed run with the right output, for every input. -/
theorem implementsRef_of_completes (ref : ByteArray → Bool) (prog : List Dec)
    (h : ∀ input : ByteArray, ∃ events,
      Completes (initState (initFfi input)) initEnv prog events ∧
        writtenBytes events = verdictBytes (ref input)) :
    ImplementsRef ref prog := by
  intro input
  obtain ⟨events, hc, hout⟩ := h input
  refine ⟨initState (initFfi input), initEnv, primSemEnv_eq _, ⟨events, hc.terminate, hout⟩, ?_⟩
  intro b hb
  exact ⟨events, hc.unique b hb, hout⟩

end ConPastel
