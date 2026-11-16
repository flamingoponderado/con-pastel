# con-pastel

> **Warning.** con-pastel is young, and nobody has reviewed it carefully. Its
> theorem is about a Lean port of CakeML's semantics that was written with AI
> assistance and has not been checked against the original (see
> [What is trusted](#what-is-trusted) and [`docs/SOUNDNESS.md`](docs/SOUNDNESS.md)).
> Distributed "as is".

con-pastel is [con-leche](https://github.com/leanprover/con-leche), the
external Lean proof checker, translated into a [CakeML](https://cakeml.org)
program. It comes with a Lean proof that the CakeML program gives the same
verdict as con-leche on every input. The program is compiled to machine code
with the **original, verified CakeML compiler**.

* The CakeML program is produced by a proof-producing translator written in
  Lean (`ConPastel/Translator`, `ConPastel/Program`), modelled on CakeML's
  `ml_translator`. It translates con-leche's pure checking pipeline
  definition by definition, and proves a refinement certificate for each one.
* The CakeML abstract syntax and source semantics come from
  [flapjack](https://github.com/flamingoponderado/flapjack), a Lean 4 port
  of CakeML.

## The theorem

```lean
theorem ConPastel.conPastel_correct (h : RuntimeAssumptions) :
    Implements conPastelProg
```

(`ConPastel/Leche/Program.lean`; the statement is in `ConPastel/Spec.lean`.)

`conPastelProg : List Flapjack.AstHOL.Dec` is the CakeML program.
`Implements` says that for every input file:

1. starting from CakeML's primitive environment (`primSemEnv`), the program,
   run under flapjack's CakeML source semantics (`semanticsProg`), terminates
   after writing `accepted\n` if con-leche accepts the file and `rejected\n`
   otherwise, and
2. that is its **only** behaviour: it never diverges, fails, or ends any
   other way.

"con-leche accepts" means that con-leche's pure pipeline returns `.ok`. The
pipeline is the composition that con-leche's own soundness theorems are
about: `builtinPreludeE`, `parseChunks`, `preparePrelude`, then
`Cached.checkDecls .verified natOpPinSets maxNatSizeDefault`, at the
parameters con-leche's shipped binary uses. con-leche's driver, command line
and parallelism are not part of it. Every con-leche outcome other than
acceptance (rejection, decline, internal error) gives `rejected`.

Input and output go through an explicit FFI model (`Stdio` in `Spec.lean`).
`read` hands out one input byte per call, and `write` records the bytes it is
given.

`RuntimeAssumptions` fixes three constants that Lean's logic leaves opaque
but that con-leche's verdict depends on, through memo tables and array
indices. They are set to what Lean v4.35.0's C runtime does:
`System.Platform.numBits = 64`, `mixHash = lean_uint64_mix_hash`, and
`String.hash = lean_string_hash` (MurmurHash64A, seed 11). The
transcriptions are checked against the runtime by `scripts/HashCheck.lean`.

`#print axioms conPastel_correct` reports only Lean's standard axioms:
`[propext, Classical.choice, Quot.sound]`.

## Running the checker

### Requirements

* x86-64 Linux, a C compiler, `make`, `curl`, `sha256sum`.
* [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.35.0)
  is pinned in `lean-toolchain`.
* Memory and time. The full Lean build (proof included) takes about 4 hours
  on 8+ cores, with peaks of about 13 GB per Lean process; four run in
  parallel at one point. Compiling with `cake` takes a 40 GB heap (set
  `CAKE_HEAP`, in MiB).

### Build

```sh
git clone <this repository> con-pastel && cd con-pastel
git submodule update --init deps/con-leche deps/flapjack   # not --recursive:
                           # flapjack's own cakeml/HOL submodules are not needed
make -C release            # produces release/build/con-pastel
```

`release/Makefile` performs four steps:

1. **Check the proof and print the program.** `lake build
   ConPastel.Leche.Program` checks `conPastel_correct`. Then
   `release/Emit.lean` prints `conPastelProg` in CakeML's S-expression
   syntax (`release/build/con-pastel.sexp`, about 31 MB) with flapjack's port
   of CakeML's printer. Before printing, it checks in the kernel that the
   printed constant equals `conPastelProg` (`Emit.prog_eq`).
2. **Fetch the CakeML compiler.** It downloads CakeML release
   [v3479](https://github.com/CakeML/cakeml/releases/tag/v3479)
   (`cake-x64-64.tar.gz`), checks its SHA-256, and links the bootstrapped
   compiler.
3. **Compile.** It runs `cake --sexp=true --exclude_prelude=true
   --skip_type_inference=true`, which turns the S-expression into x86-64
   assembly (`release/build/con-pastel.S`).
4. **Link.** It links the assembly with `release/con_pastel_ffi.c`, which
   implements the `read`/`write` FFI model and CakeML's runtime entry point.

Each step can be run on its own: `make -C release sexp`, `cake`, or
`build/con-pastel.S`.

### Run

```sh
lean4export … > export.ndjson     # any lean4export output that con-leche reads
release/build/con-pastel < export.ndjson
```

The checker prints `accepted` or `rejected`, then exits with code 0. Only
output from a run that exits with code 0 is a verdict:

| exit code | meaning |
|---|---|
| 0 | the output is the verdict |
| 1, 2 | CakeML ran out of heap or stack before finishing; no verdict. Rerun with a larger `CML_HEAP_SIZE` / `CML_STACK_SIZE` (MiB; defaults are 16384 and 4096). |
| 3 | the runtime could not allocate the heap and stack |
| 4 | an FFI failure (an I/O error) |

CakeML's compiler correctness theorem allows the program to stop early when
it runs out of resources. It does not allow any other deviation.

### Test

```sh
make -C release test
```

This runs the checker on con-leche's end-to-end fixtures
(`deps/con-leche/tests/e2e`) and compares each verdict with con-leche's
expected result (`tests/e2e-expected.txt`). Gzipped fixtures, fixtures over
1 MB and timeout fixtures are skipped by default; see `release/test.sh`.

## What is trusted

The complete list of gaps, unverified components, trusted components and
assumptions is in [`docs/SOUNDNESS.md`](docs/SOUNDNESS.md). This section
summarises it.

The chain from "con-leche accepts" to "this executable prints `accepted`"
has five links. Each one is either proved or trusted:

| link | status |
|---|---|
| con-leche's pipeline ↔ `conPastelProg` under flapjack's CakeML semantics | **proved in Lean** (`conPastel_correct`) |
| flapjack's CakeML semantics ↔ CakeML's original HOL4 semantics | **trusted**: AI-assisted port, not reviewed, no equivalence proof |
| `conPastelProg` (Lean) ↔ the program `cake` parses | partly checked; trusts flapjack's S-expression printer |
| the program ↔ the machine code | **proved in HOL4** (CakeML's backend correctness theorem), up to the conditions listed below |
| the machine code ↔ the running process | trusted: CakeML's x86-64 model, the assembler and linker, `con_pastel_ffi.c`, OS and hardware |

In more detail:

1. **Lean.** The Lean kernel, the three standard axioms, and the statement
   in `ConPastel/Spec.lean`. Read `Spec.lean`: it fixes what "the same
   verdict as con-leche" means (the pure pipeline, the FFI model, the output
   bytes).
2. **The runtime assumptions** about Lean's compiled code (above). They
   describe the reference: con-leche as Lean compiles it. They say nothing
   about CakeML.
3. **flapjack's CakeML source semantics (the largest gap).** `semanticsProg`,
   `evaluate`, `primSemEnv`, and the semantic primitives in
   `deps/flapjack/Flapjack/{SemanticsHOL,EvaluateHOL,SemanticPrimitivesHOL,...}`
   were ported from CakeML's HOL4 sources (commit `857f0d98`) with heavy AI
   assistance ("vibe-ported"). Nobody has reviewed them line by line, and no
   theorem relates them to the HOL4 originals; see flapjack's
   `docs/SOUNDNESS.md`. `conPastel_correct` is a theorem about the *Lean*
   meaning of the program. If the port gives some construct used by
   `conPastelProg` a different meaning from the original, then the
   theorem says nothing about how the original compiler's output behaves.
   The program uses a small part of the language: closures, `letrec`,
   `let`, `if`, pattern matching, datatype constructors, bignum integer
   arithmetic, equality, a 2-byte byte array, and the `read`/`write` FFI
   calls. It has no exceptions, references, or string or machine-word
   operations (`docs/SOUNDNESS.md`, item 1).
4. **From Lean to `cake`.** `release/Emit.lean` prints the program with
   flapjack's ports of HOL4's `decsexp` encoder and `print_sexp` printer
   (`Flapjack.CakeParser.ToSexp`, `Sexp.render`). In HOL4,
   `sexpdec_decsexp` and `parse_print` show that the original `cake`
   decodes printed bytes back to the printed AST. What is trusted is that
   flapjack's encoder maps each Lean `Dec` to the HOL4 `dec` with the same
   meaning: a one-to-one, constructor-by-constructor mapping. The printing
   also runs as compiled Lean code, so Lean's code generator is trusted for
   this step (`docs/SOUNDNESS.md`, item 3).
   `make -C release check-sexp` asks the original `cake` to print back the
   program it parsed (`--print_sexp`) and compares that byte-for-byte with
   the emitted file.
5. **The original CakeML compiler.** We use CakeML's own release binary,
   bootstrapped inside HOL4. Release v3479 (commit `e8eca63`) is 28 commits
   behind flapjack's reference commit `857f0d98`. Those commits change only
   Pancake command-line flags and examples. They touch neither the source
   semantics nor the CakeML compiler passes.

   The theorem that applies is the backend correctness theorem
   `backendProof.compile_correct`. If `compile` returns machine code, and
   the program's semantics from `prim_sem_env` **does not include `Fail`**,
   then every machine behaviour is a source behaviour or a prefix of one
   that stops because resources ran out. CakeML's top-level
   `compilerProof.compile_correct` also covers parsing and type inference,
   but it requires concrete syntax and type inference to be on.
   con-pastel's program is untyped: the translator writes datatype fields
   as unconstrained type variables, so `cake` must skip type inference.
   Type inference exists to establish "no `Fail`", and `conPastel_correct`
   proves exactly that, but only under flapjack's semantics (item 3).
   Trusting HOL4's result also means trusting HOL4's kernel and CakeML's
   x86-64 ISA model.
6. **The executable.** The GNU assembler and linker, `release/con_pastel_ffi.c`
   (it must implement `stdioOracle` from `Spec.lean`, including how the
   program uses its 2-byte read buffer), the C library, the OS and the CPU.

## Closing the gaps

The weakest links are item 3 (the ported semantics) and item 4 (the printer).
The plan is to remove both from the trusted base, using flapjack's port of
the CakeML **compiler**, which is in progress in the flapjack repository.

### Step 1: identical machine code from both compilers

flapjack is porting the CakeML compiler (its front end, the passes from
source to the backend languages, and the target encoders) to Lean, together
with its correctness theorems. The first goal is to compile the *same*
S-expression with both compilers:

* the original `cake` (HOL4, release binary), giving machine code `M₁`;
* flapjack's `cake` (Lean), giving machine code `M₂`;

and to observe `M₁ = M₂` byte for byte. flapjack already runs this kind of
byte-level parity testing for Pancake on RISC-V, ARMv8 and x86-64. Its CakeML
front end currently targets RISC-V, so the comparison would use
`--target=riscv` on both sides until the x86-64 path is ported.

### Step 2: trust only the machine-code semantics

Suppose `M₁ = M₂ = M`. Each compiler's correctness theorem says that `M`
implements the program under that compiler's own source semantics:

* HOL4: `machine_sem_HOL M ⊆ extend_with_resource_limit (semantics_prog_HOL P)`
* Lean: `machine_sem_Lean M ⊆ extend_with_resource_limit (semanticsProg_Lean P)`

`conPastel_correct` pins down `semanticsProg_Lean P`: it terminates with
con-leche's verdict. Composing it with flapjack's compiler theorem gives a
Lean statement about `M`, under `machine_sem_Lean`, in which flapjack's
source semantics is only an intermediate step. A wrong porting choice there
cannot make the composed statement false, because both theorems use the same
definition.

What remains trusted is that the Lean and HOL4 machine-code semantics agree
on `M`, together with the step `M₂ = compile P`. Machine-code semantics are
much smaller and easier to compare than a source semantics, and flapjack
already compares its RISC-V model against Sail in a separate project. When
they agree, the two compiler theorems also show that the HOL4 and Lean
source semantics give *this particular* program the same observable
meaning, since both are refined by the same machine code. That is an
after-the-fact check on the vibe-ported semantics, made for exactly the
program that matters.

Until flapjack's compiler theorem covers the CakeML front end, this step
also trusts that flapjack's `cake` is the compiler its theorem is about.
Today this holds for the Pancake chain, not yet for CakeML source.

### Step 3: run the ported compiler in the Lean kernel

Step 2 still observes `M₂ = compile P` by *running* flapjack's compiler
outside the logic. The last step is to prove

```lean
theorem compile_conPastel : Flapjack.compile cfg conPastelProg = some (M, …)
```

by evaluation in the Lean kernel. Instantiating flapjack's compiler
correctness theorem with it, and with `conPastel_correct` (which also
discharges the "no `Fail`" premise), gives one Lean theorem:

```lean
theorem conPastel_machine_code (h : RuntimeAssumptions) :
    ∀ input, machine_sem M (stdio input) ⊆
      extend_with_resource_limit {terminate with verdictBytes (conLecheAccepts input)}
```

This theorem says the machine code behaves like con-leche, up to running out
of memory. Its trusted base is the Lean kernel, `Spec.lean`, the machine-code
semantics, and what lies below it (the assembler, `con_pastel_ffi.c`, the OS
and hardware). The CakeML source semantics and the S-expression printer
leave the trusted base entirely.

This mirrors how CakeML bootstraps itself in HOL4, where the compiler is
evaluated inside the logic (`cv_compute`) on its own source. The main work:

* **Kernel evaluation at scale.** The program is about 3,500 functions and
  183k AST nodes after sharing, and the whole compiler has to run on it.
  Plain `decide`/`rfl` reduction is far too slow. The likely route is a
  reflective, compiled-evaluation design: Lean's kernel has GMP-accelerated
  `Nat` and `String` literals, and con-pastel already avoids kernel-costly
  operations (see `ConPastel/Program/Scale.lean`). The compilation would be
  split into per-pass and per-function lemmas, so that each kernel check
  stays small and can be cached.
* **The compiler theorem's side conditions** in Lean: configuration
  well-formedness, FFI names, initial machine state. The "no `Fail`" premise
  comes from `conPastel_correct`, so no type inference is needed.
* **Getting `M` out.** The bytes in the theorem are written to an assembly
  file in CakeML's export format and linked with `con_pastel_ffi.c`, as in
  this release.

## Repository layout

| path | contents |
|---|---|
| `ConPastel/Spec.lean` | the correctness statement (read this first) |
| `docs/SOUNDNESS.md` | gaps, unverified components, trusted components and assumptions |
| `ConPastel/Translator/` | the proof-producing Lean → CakeML translator |
| `ConPastel/Semantics/` | lemmas about flapjack's CakeML semantics |
| `ConPastel/Main/` | the hand-written I/O wrapper (read input, write verdict) and its proof |
| `ConPastel/Program/` | assembling all translated units into one program (`cake_program`) |
| `ConPastel/Leche/` | the translation of con-leche, and the final theorem (`Program.lean`) |
| `ConPastel/Examples/` | small translator examples |
| `release/` | building and testing the executable with the original CakeML compiler |
| `deps/con-leche`, `deps/flapjack` | the checker being ported, and the CakeML port |
| `PLAN.md` | the development plan and its history |

## License

See `LICENSE`.
