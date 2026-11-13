import ConPastel.Spec
import Flapjack.SemanticsProps.Determinism

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

/-- `Implements` from a completed run with the right output, for every input. -/
theorem implements_of_completes (prog : List Dec)
    (h : ∀ input : ByteArray, ∃ st env,
      PrimTypesHOL.primSemEnv (initFfi input) = some (st, env) ∧
      ∃ events, Completes st env prog events ∧
        writtenBytes events = verdictBytes (conLecheAccepts input)) :
    Implements prog := by
  intro input
  obtain ⟨st, env, hprim, events, hc, hout⟩ := h input
  refine ⟨st, env, hprim, ⟨events, hc.terminate, hout⟩, ?_⟩
  intro b hb
  exact ⟨events, hc.unique b hb, hout⟩

end ConPastel
