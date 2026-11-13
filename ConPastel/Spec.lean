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

/-! ## Runtime assumptions

Some constants that con-leche's pipeline reaches are opaque in Lean's logic:
the logic does not determine their values, only the compiled code does. Two
of them influence con-leche's accepting path, through memo tables and array
indices, so the final theorem assumes what the Lean runtime does for them,
transcribed from Lean v4.35.0's C runtime:

* `System.Platform.numBits` (the width of `USize`) is 64;
* `mixHash` is `lean_uint64_mix_hash` (`src/include/lean/lean.h`);
* `String.hash` is `lean_string_hash` (`src/runtime/object.cpp`): MurmurHash64A
  (`src/runtime/hash.cpp`) with seed 11 over the string's UTF-8 bytes, with
  8-byte blocks read little-endian.

Other opaque constants on the path do not need assumptions: they only
contribute to error contents (`Expr.hasStrLitGo`, the messages of `panic!`),
which never affect the verdict, or they are terminating `while` loops, whose
value Lean's logic does pin down (`repeatM`). -/

/-- `lean_uint64_mix_hash`. -/
def leanMixHash (h k : UInt64) : UInt64 :=
  let m : UInt64 := 0xc6a4a7935bd1e995
  let k := k * m
  let k := k ^^^ (k >>> 47)
  let k := k ^^^ m
  let h := h ^^^ k
  h * m

/-- Little-endian value of up to 8 bytes. -/
def leWord (bs : List UInt8) : UInt64 :=
  (bs.zipIdx).foldl (fun acc (b, i) => acc ^^^ (b.toUInt64 <<< (8 * i).toUInt64)) 0

/-- The 8-byte block loop of MurmurHash64A. -/
def murmurBlocks (m : UInt64) (h : UInt64) : List UInt8 → UInt64 × List UInt8
  | b₀ :: b₁ :: b₂ :: b₃ :: b₄ :: b₅ :: b₆ :: b₇ :: rest =>
    let k := leWord [b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇]
    let k := k * m
    let k := k ^^^ (k >>> 47)
    let k := k * m
    murmurBlocks m ((h ^^^ k) * m) rest
  | tail => (h, tail)

/-- MurmurHash64A (`src/runtime/hash.cpp`). -/
def murmurHash64A (bytes : List UInt8) (seed : UInt64) : UInt64 :=
  let m : UInt64 := 0xc6a4a7935bd1e995
  let h := seed ^^^ (bytes.length.toUInt64 * m)
  let (h, tail) := murmurBlocks m h bytes
  let h := if tail.isEmpty then h else (h ^^^ leWord tail) * m
  let h := h ^^^ (h >>> 47)
  let h := h * m
  h ^^^ (h >>> 47)

/-- `lean_string_hash`. -/
def leanStringHash (s : String) : UInt64 :=
  murmurHash64A s.toByteArray.toList 11

/-- What the final theorem assumes about the Lean runtime. -/
structure RuntimeAssumptions : Prop where
  numBits : System.Platform.numBits = 64
  mixHash : ∀ h k, mixHash h k = leanMixHash h k
  stringHash : ∀ s, String.hash s = leanStringHash s

end ConPastel
