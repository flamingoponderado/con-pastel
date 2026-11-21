import ConPastel.Spec

/-!
# The FFI model of one process of the parallel checker

The parallel checker runs the same CakeML program in several processes (`docs/PARALLEL-PLAN.md`).
Each process is a run of the program under CakeML's semantics with its own FFI oracle, `parOracle`,
whose state `ParIO` is the script of everything the harness answers that process:

* `input`: the input bytes, served by `read` as in `stdioOracle`;
* `worker`: `spawn`'s answer, `false` in the parent, `true` in a worker;
* `claims`: the answers of successive `claim` calls, 8 bytes each (an index, little-endian);
* `table`: the job codes `results` serves, with `read`'s protocol.

A process's actual run is its run under the script of the answers it actually got (the oracle is
consulted only through these calls), so a statement for every script is a statement for every
harness behaviour. `report` records its configuration and buffer in the io-event and changes
nothing; `write` is `stdioOracle`'s. Every other call (`abort` among them), a `claim` with no
answer left, and a buffer of the wrong size end the run with an FFI failure.

The FFI contract this model encodes: a call changes only the bytes of the array it is passed (same
length) and the oracle state. The harness's shared memory lives outside the CakeML heap and is
copied in and out by the calls; no pointer is passed back.
-/

namespace ConPastel.Par
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- The script of one process's FFI answers. -/
structure ParIO where
  input : List (BitVec 8)
  worker : Bool
  claims : List (List (BitVec 8))
  table : List (BitVec 8)

/-- The `read` protocol over a stream of bytes: `1` and the next byte, or `0` at the end. -/
def streamAnswer (rest : List (BitVec 8)) (bytes : List (BitVec 8)) :
    List (BitVec 8) × List (BitVec 8) :=
  match rest with
  | b :: r => (r, 1 :: b :: bytes.drop 2)
  | [] => ([], 0 :: bytes.drop 1)

/-- **The FFI oracle of one process.** -/
def parOracle : HolOracle ParIO
  | .extCall name, st, _conf, bytes =>
    if name = ofString "read" then
      if 2 ≤ bytes.length then
        let (r, out) := streamAnswer st.input bytes
        .ret { st with input := r } out
      else .final .failed
    else if name = ofString "write" then
      .ret st bytes
    else if name = ofString "spawn" then
      if bytes.length = 9 then .ret st ((if st.worker then 1 else 0) :: bytes.drop 1)
      else .final .failed
    else if name = ofString "claim" then
      if bytes.length = 9 then
        match st.claims with
        | c :: rest => if c.length = 8 then .ret { st with claims := rest } (bytes.take 1 ++ c)
                       else .final .failed
        | [] => .final .failed
      else .final .failed
    else if name = ofString "report" then
      if bytes.length = 9 then .ret st bytes else .final .failed
    else if name = ofString "results" then
      if 2 ≤ bytes.length then
        let (r, out) := streamAnswer st.table bytes
        .ret { st with table := r } out
      else .final .failed
    else .final .failed
  | .sharedMem _, _, _, _ => .final .failed

/-- The initial FFI state of a process. -/
def initParFfi (io : ParIO) : HolFfiState ParIO := initialHolFfiState parOracle io

end ConPastel.Par
