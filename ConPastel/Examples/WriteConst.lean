import ConPastel.Semantics.Behaviour
import ConPastel.Semantics.Init
import Batteries.Tactic.OpenPrivate

/-!
# Milestone 1 check: a program that always writes `accepted\n`

`writeAccepted` calls the `write` FFI once with the configuration
`"accepted\n"` on a fresh empty byte array. It completes on every input with
exactly the bytes `verdictBytes true`. This exercises `primSemEnv_eq`,
evaluating through the FFI model, and `Completes`.
-/

namespace ConPastel.Examples
open Flapjack Flapjack.AstHOL Flapjack.SemanticsHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.EvaluateHOL Flapjack.Basis.Pure.MlString Flapjack.Misc.Location
open private everyExpList from Flapjack.AstHOL.Syntax

def writeAccepted : List Dec :=
  [.dlet unknownLoc .pany
    (.app (.ffi (ofString "write"))
      [.lit (.strLit (ofString "accepted\n")), .app .aw8alloc [.lit (.intLit 0), .lit (.word8 0)]])]

/-- The event the program produces. -/
def writeEvent : HolIoEvent :=
  { name := .extCall (ofString "write"), configuration := verdictBytes true, bytes := [] }

theorem writeAccepted_eval (input : ByteArray) :
    evaluateProgWithClock (initState (initFfi input)) initEnv 0 writeAccepted =
      ({ initFfi input with ioEvents := [writeEvent] }, .val { v := .bind [] [], c := .bind [] [] }) := by
  simp +decide [evaluateProgWithClock, writeAccepted, evaluateDecs, evaluate, fixClock,
    initState, initFfi, getOpClass, everyExp, everyExpList, oneConCheck, headValue,
    Flapjack.holHd, doApp, doAppNumericCore, doAppBasic, storeAlloc, storeLookup, storeAssign,
    callFFIHOL, stdioOracle, listResult, initialHolFfiState, storeValueSameType, pmatch,
    writeEvent, verdictBytes, NamespaceHOL.alistToNs, NamespaceHOL.nsEmpty]

theorem writeAccepted_completes (input : ByteArray) :
    Completes (initState (initFfi input)) initEnv writeAccepted [writeEvent] :=
  ⟨0, _, _, writeAccepted_eval input, by simp, by simp, by simp, rfl⟩

theorem writeAccepted_output : writtenBytes [writeEvent] = verdictBytes true := by
  simp [writtenBytes, writeEvent]

end ConPastel.Examples
