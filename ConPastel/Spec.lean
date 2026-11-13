import Flapjack.SemanticsHOL
import Flapjack.PrimTypesHOL
import ConLeche.MainTheorem

/-!
# The con-pastel correctness statement

This file fixes what "the CakeML program behaves the same as con-leche"
means. The final theorem of con-pastel is `Implements conPastelProg`.

* **Reference.** con-leche's pure pipeline, the same composition its
  `no_False_declaration` and `main_no_False` are about: parse the export
  bytes (`parseChunks`), prepare the prelude (`preparePrelude`), then run the
  declaration fold (`checkDecls`) in `.verified` mode at the pins and
  maximum Nat size the shipped binary uses. The verdict is whether that
  returns `.ok`.
* **Implementation.** A CakeML program, run by flapjack's port of the CakeML
  source semantics (`semanticsProg`) from the primitive environment
  (`primSemEnv`).
* **Input and output** go through a small, explicit FFI model (`Stdio`).
  `read` hands out input bytes in chunks and `write` records output bytes.
  The verdict is the bytes the program writes.
-/

namespace ConPastel
open Flapjack Flapjack.AstHOL Flapjack.SemanticsHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Basis.Pure.MlString

/-! ## Reference: con-leche's verdict -/

open ConLeche ConLeche.Frontend in
/-- con-leche's pure pipeline on one export file, exactly the composition in
`ConLeche.no_False_declaration`, at the shipped binary's parameters (see
`ConLeche.main_no_False`). -/
def conLecheResult (input : ByteArray) : Except (CheckError × Nat) Env := do
  let pre ← builtinPreludeE
  let r ← parseChunks [input]
  let ds := preparePrelude pre r.decls
  Cached.checkDecls .verified natOpPinSets Cached.maxNatSizeDefault ds

/-- Whether con-leche accepts the export file. -/
def conLecheAccepts (input : ByteArray) : Bool :=
  match conLecheResult input with
  | .ok _ => true
  | .error _ => false

/-! ## The FFI model -/

/-- Host state of the FFI model: the input bytes not yet read. Output is
read back from the event trace instead. -/
structure Stdio where
  input : List (BitVec 8)

/-- Encode `n` as 8 little-endian bytes. -/
def le64 (n : Nat) : List (BitVec 8) :=
  (List.range 8).map fun i => BitVec.ofNat 8 (n / 256 ^ i)

/-- The FFI oracle.

* `read`, called with a buffer of length `8 + k`: let `n = min k remaining`.
  The oracle writes `n` as 8 little-endian bytes into the buffer, then the
  next `n` input bytes, and leaves the rest of the buffer unchanged.
  `n = 0` means end of input.
* `write`, called with the bytes to write as configuration: the buffer is
  returned unchanged and nothing else changes. The written bytes are
  recorded in the io-event (`HolIoEvent.configuration`).
* Every other name, and a `read` buffer shorter than 8 bytes, ends the run
  with an FFI failure.
-/
def stdioOracle : HolOracle Stdio
  | .extCall name, st, _conf, bytes =>
    if name = ofString "read" then
      if 8 ≤ bytes.length then
        let n := min (bytes.length - 8) st.input.length
        .ret { input := st.input.drop n }
          (le64 n ++ st.input.take n ++ bytes.drop (8 + n))
      else .final .failed
    else if name = ofString "write" then
      .ret st bytes
    else .final .failed
  | .sharedMem _, _, _, _ => .final .failed

/-- The initial FFI state for an input file. -/
def initFfi (input : ByteArray) : HolFfiState Stdio :=
  initialHolFfiState stdioOracle { input := input.toList.map (·.toBitVec) }

/-- Everything the program wrote, in order. -/
def writtenBytes (events : List HolIoEvent) : List (BitVec 8) :=
  events.flatMap fun e =>
    if e.name = .extCall (ofString "write") then e.configuration else []

/-- The output that stands for each verdict (ASCII, one byte per character). -/
def verdictBytes (accepted : Bool) : List (BitVec 8) :=
  (if accepted then "accepted\n" else "rejected\n").toList.map fun c => BitVec.ofNat 8 c.toNat

/-! ## The statement -/

/-- **The con-pastel correctness statement** for a CakeML program `prog`.

For every input file, starting from the primitive environment:
1. the program has a terminating behaviour whose written bytes are
   con-leche's verdict, and
2. that is its only behaviour: it never diverges, fails, or terminates
   any other way, including with a different output.

The CakeML source semantics is idealised (unbounded memory, bignums), so
this says nothing about resource limits; flapjack's compiler theorems
handle those separately. -/
def Implements (prog : List Dec) : Prop :=
  ∀ input : ByteArray, ∃ st env,
    PrimTypesHOL.primSemEnv (initFfi input) = some (st, env) ∧
    (∃ events, semanticsProg st env prog (.terminate .success events) ∧
      writtenBytes events = verdictBytes (conLecheAccepts input)) ∧
    ∀ b, semanticsProg st env prog b →
      ∃ events, b = .terminate .success events ∧
        writtenBytes events = verdictBytes (conLecheAccepts input)

end ConPastel
