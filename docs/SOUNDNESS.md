# Soundness status

This document lists what con-pastel proves, what it assumes, what it
trusts, and what is not yet verified. It is written conservatively. A
theorem that elaborates in Lean, and an executable that passes tests, are
not by themselves evidence that the executable behaves like con-leche.

The claim con-pastel aims at is: *the executable `release/build/con-pastel`,
given a lean4export file on standard input, prints `accepted` exactly when
con-leche accepts the file.* The chain behind it, and the status of each
link:

| # | link | status |
|---|---|---|
| A | con-leche's pure pipeline ↔ `conPastelProg` under flapjack's CakeML semantics | proved in Lean (`conPastel_correct`) |
| B | flapjack's CakeML semantics ↔ CakeML's HOL4 semantics | **trusted, unverified** |
| C | `conPastelProg` (Lean value) ↔ the bytes of `con-pastel.sexp` | trusted (Lean's compiler, flapjack's printer) |
| D | `con-pastel.sexp` ↔ the AST that `cake` compiles | HOL4 theorems, plus a byte-for-byte cross-check |
| E | AST ↔ x86-64 machine code | proved in HOL4 (CakeML backend), conditions below |
| F | machine code ↔ the running process | trusted (ISA model, toolchain, FFI C code, OS, CPU) |

The items below are numbered for reference. They are not ranked, except
that item 1 is the largest gap.

## Gaps and unverified components

1. **flapjack's CakeML source semantics is a vibe-port (link B).**
   `Flapjack.SemanticsHOL.semanticsProg`, `EvaluateHOL`,
   `SemanticPrimitivesHOL`, `PrimTypesHOL.primSemEnv` and the FFI model
   behind them were ported from CakeML's HOL4 sources (commit `857f0d98`)
   with heavy AI assistance. They have not been reviewed line by line, and
   no theorem relates them to HOL4 (HOL-to-Lean equivalence is out of scope
   for flapjack; see `deps/flapjack/docs/SOUNDNESS.md`). `conPastel_correct`
   is a statement about the Lean definitions only. A porting mistake in
   any construct `conPastelProg` uses could make the theorem true while the
   compiled program behaves differently. The program uses a small part of
   the language, which narrows what needs reviewing. Counted in the emitted
   S-expression:
   * declarations: one `Dtype` (383 datatypes), two `Dletrec` (one with
     3,472 functions), three `Dlet`;
   * expressions: `Fun`, `App Opapp`, `Var`, `Con`, `Lit` (integers, two
     `word8` literals, one string), `Let`, `If`, `Mat`;
   * patterns: constructor (`Pcon`), variable and wildcard;
   * primitives: integer `+ - * div mod < ≤` (`Arith`/`Test` at `IntT`),
     `Equality`, `Aw8alloc`, `Aw8sub`, `FromTo Word8T IntT`, and the FFI
     calls `read` and `write`.

   There are no exceptions (`Raise`, `Handle`), no `Log`, no string or
   machine-word arithmetic, and no references. con-leche's machine words,
   strings and arrays are translated to datatypes and bignum integers. Plan:
   README, "Closing the gaps", steps 2 and 3.

2. **HOL choice operators** are translated in flapjack with Lean's
   classical choice (`holOptionSome`, `buildLprefixLub`). `semanticsProg`
   uses this for diverging behaviours (lprefix lubs). That is no new Lean
   axiom (`Classical.choice` is standard), but agreement with HOL4's
   `@`-terms is assumed, not shown.

3. **The bytes of the S-expression are computed by Lean's compiled code
   (link C).** `release/Emit.lean` checks in the kernel that the constant it
   prints is `conPastelProg` (`Emit.prog_eq`, by `rfl`). The printing
   itself (`ToSexp.program`, `Sexp.render`) then runs as compiled code,
   through Lean's code generator and runtime, and is not kernel-checked. A
   bug in Lean's compiler, or in the native compilation of these functions,
   could print a different program. The cross-check in item 5 does not
   catch this, because it compares the printed file with itself
   round-tripped through `cake`.

4. **flapjack's S-expression encoder is trusted to match HOL4's (link C).**
   `Flapjack.CakeParser.ToSexp` and `Sexp.render` are ports of HOL4's
   `decsexp` (`fromSexpScript.sml`) and `print_sexp`
   (`simpleSexpParseScript.sml`). flapjack proves its own decoder inverts
   its encoder (`decodeDec_decsexp`, `decsexp_injective`), but nothing
   proves that the port encodes a Lean `Dec` the way HOL4 encodes the
   corresponding HOL `dec`. What is trusted: the encoding is
   constructor-for-constructor and maps each Lean constructor to the HOL
   constructor of the same meaning. This overlaps with item 1, since the
   AST types are part of the port.

5. **Parsing in the original `cake` (link D).** `cake --sexp=true` parses
   with HOL4's `parse_sexp` and decodes with `sexplist sexpdec`. HOL4
   proves `parse_print` (`parse_sexp (print_sexp s) = SOME s` for valid
   `s`) and `sexpdec_decsexp`. So if the file is HOL4's printing of an AST,
   `cake` compiles that AST. The cross-check `make -C release check-sexp`
   has the original `cake` print back what it parsed (`--print_sexp`) and
   compares the result byte-for-byte with the emitted file. This is
   evidence that the file is in HOL4's canonical printed form. It does not
   replace items 3 and 4. This path is *not* covered by CakeML's top-level
   compiler theorem (item 6).

6. **The CakeML compiler theorem that applies has a semantic premise
   (link E).** CakeML's top-level theorem `compilerProof.compile_correct`
   requires concrete-syntax input and type inference
   (`¬input_is_sexp ∧ ¬skip_type_inference`). con-pastel uses neither:
   * the translator emits an untyped program (datatype fields are
     unconstrained type variables), so `cake` runs with
     `--skip_type_inference=true`, and its type checker would reject the
     program;
   * input is an S-expression (`--sexp=true`).

   What applies is the backend theorem `backendProof.compile_correct`, for
   the program `cake` parsed, from `prim_sem_env`, with the premise
   `¬semantics_prog s env prog Fail`. In CakeML that premise normally
   comes from type soundness. Here it comes from `conPastel_correct`, which
   shows that the only behaviour is successful termination. That makes
   the premise depend on item 1: it is proved for flapjack's semantics,
   not HOL4's.

7. **The CakeML release (link E).** The compiler is CakeML's release v3479
   (`cake-x64-64.tar.gz`, SHA-256 `e110bfcb…1c9a`, commit `e8eca63`). It
   is a binary produced by CakeML's in-logic bootstrap in HOL4. Trusted:
   the release artefact is what CakeML's build produced, the HOL4 kernel,
   the bootstrap's evaluation in HOL4, and that the release's theorems are
   the ones in the CakeML repository at that commit. flapjack's reference
   commit is `857f0d98`, 28 commits later. The difference is confined to
   Pancake command-line flags (`--pancake_feature`) and examples. The
   source semantics, the CakeML front end and the backend are unchanged.

8. **CakeML's machine model and resource limits (links E, F).** The
   backend theorem is about CakeML's x86-64 ISA model and an
   `installed`/`mc_init_ok` machine configuration. Trusted: the model
   matches the CPU on the emitted instructions, and the startup code
   together with `con_pastel_ffi.c` establishes the theorem's
   initial-state conditions (heap and stack layout, registers, FFI entry
   points). The theorem's conclusion is `extend_with_resource_limit`: the
   process may stop early when it runs out of heap or stack, after
   writing a prefix of its output. Such runs exit with code 1 or 2 and
   carry no verdict. Users must treat only exit code 0 as a verdict.

9. **The FFI implementation is trusted (link F).**
   `release/con_pastel_ffi.c` must implement `stdioOracle` from
   `ConPastel/Spec.lean`: `read` puts a status byte and a data byte in a
   buffer of at least 2 bytes, and `write` outputs exactly its
   configuration bytes. The correspondence between the C code and the
   oracle is checked by reading, not by proof. The C library's stdio, the
   assembler, the linker, the OS and the CPU are trusted.

## Assumptions in the theorem statement

10. **`RuntimeAssumptions`.** `System.Platform.numBits = 64`; `mixHash` and
    `String.hash` equal transcriptions of Lean v4.35.0's C runtime
    (`lean_uint64_mix_hash`, MurmurHash64A with seed 11). These constants
    are opaque in Lean's logic but affect con-leche's verdict, through memo
    tables and array indices. The assumptions describe the reference, which
    is con-leche as Lean compiles it, so the theorem matches the shipped
    con-leche binary only on a 64-bit Lean runtime with these hash
    functions. `scripts/HashCheck.lean` tests the transcriptions against
    the runtime; that is a test, not a proof.

11. **Other opaque constants need no assumption.** `Expr.hasStrLitGo` and
    `panic!` messages only shape error contents, which the verdict ignores.
    The translator refines them with a trivial invariant. Terminating
    `while` loops (`repeatM`) and `WellFounded.extrinsicFix` are pinned by
    Lean's logic. This is part of the proof, not trusted, and is listed
    here because the reasoning is subtle.

## What "the same as con-leche" covers

12. **Scope of the reference.** The reference is con-leche's pure pipeline
    (`ConPastel.conLecheResult`): `builtinPreludeE`, `parseChunks`,
    `preparePrelude`, `Cached.checkDecls .verified natOpPinSets
    maxNatSizeDefault`. con-leche's driver, command line, parallel
    checking, file handling and exit-code logic are not modelled. A
    difference between the shipped con-leche binary and this pipeline is
    outside the theorem.

13. **Verdicts are collapsed.** con-leche distinguishes accept, reject,
    decline and internal error (exit codes 0–3). con-pastel prints
    `accepted` for `.ok` and `rejected` for every error.

14. **Pinned versions.** con-leche `6810492c1` (`deps/con-leche`), flapjack
    branch `lean-v4.35.0` at `9c95326186` (`deps/flapjack`), Lean v4.35.0.
    The theorem is about these exact sources.

15. **con-leche's own soundness is separate.** con-pastel shows that the
    CakeML program agrees with con-leche. Whether con-leche itself only
    accepts correct proofs is con-leche's claim (`no_False_declaration`,
    `main_no_False`), with con-leche's own trust base.

## Not trusted (checked by Lean)

* The translator (`ConPastel/Translator`, `ConPastel/Program`). It is a
  proof-producing metaprogram, and every certificate it emits is checked by
  the Lean kernel. A translator bug can make the build fail, but cannot
  produce a false theorem.
* The I/O wrapper (`ConPastel/Main`): hand-written CakeML with a Lean proof.
* Axioms: `#print axioms ConPastel.conPastel_correct` gives
  `[propext, Classical.choice, Quot.sound]`. The Lean kernel itself is
  trusted.

## Evidence beyond proofs

* `make -C release check-sexp`: the original `cake` parses exactly the
  emitted program (item 5).
* `make -C release test`: verdicts of the CakeML executable on
  con-leche's end-to-end fixtures, compared with con-leche's expected
  results. Fixtures are regression evidence. They do not establish
  equivalence for all inputs.

## Planned reductions of the trusted base

See README, "Closing the gaps". In short:

1. Compile the same S-expression with flapjack's Lean port of the CakeML
   compiler, and observe identical machine code to the original `cake`.
2. Compose flapjack's compiler correctness theorem with
   `conPastel_correct`, so that the CakeML source semantics (items 1, 2, 6)
   becomes an internal step of a Lean proof rather than a trusted
   component. What remains trusted is that the Lean and HOL4 machine-code
   semantics agree on the emitted code.
3. Evaluate the ported compiler in the Lean kernel (`compile P = M`). This
   removes the out-of-logic printing and parsing (items 3, 4, 5) and gives
   one Lean theorem relating the machine code to con-leche.
