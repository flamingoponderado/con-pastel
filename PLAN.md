# con-pastel plan

## Goal

Prove, in Lean, `theorem conPastel_correct : ConPastel.Implements conPastelProg`
(statement in `ConPastel/Spec.lean`), where `conPastelProg : List Flapjack.AstHOL.Dec`
is a CakeML program obtained from con-leche's checker.

`Implements` says: for every input file fed through the `Stdio` FFI model,
starting from `primSemEnv`, the program's only behaviour under flapjack's
`semanticsProg` is successful termination writing `accepted\n` or `rejected\n`,
matching con-leche's pure pipeline (`parseChunks` → `preparePrelude` →
`checkDecls .verified natOpPinSets maxNatSizeDefault`).

The goal is reached when `lake build` checks `conPastel_correct` with no
`sorry`, and `#print axioms conPastel_correct` shows only Lean's standard
axioms (plus whatever flapjack's semantics already depends on, listed explicitly).

## Opaque constants (found 2026-11-13)

con-leche's pipeline reaches constants that Lean's logic leaves undetermined.
The final theorem therefore has the hypothesis `RuntimeAssumptions` (in
`ConPastel/Spec.lean`): `System.Platform.numBits = 64`, and `mixHash` /
`String.hash` equal transcriptions of Lean's C runtime (checked against the
runtime by `scripts/HashCheck.lean`). Other opaque constants need no
assumption: `Expr.hasStrLitGo` and `panic!` messages only shape error
contents, which the translator refines with a trivial invariant (the verdict
only looks at ok/error); terminating `while` loops (`repeatM`) and
`WellFounded.extrinsicFix` are pinned by Lean's logic.

The goal statement becomes
`theorem conPastel_correct (h : RuntimeAssumptions) : Implements conPastelProg`.

## Decisions (fixed)

- Scope: the pure pipeline only; con-leche's driver, CLI and parallelism are not ported.
- Approach: a proof-producing translator in Lean, modelled on CakeML's
  `ml_translator`, emitting `AstHOL.Dec` plus refinement certificates.
- Equivalence: same accept/reject verdict, observed via written bytes.
- Toolchain: Lean v4.35.0 (con-leche's); flapjack is used from its
  `lean-v4.35.0` branch.

## Milestones

Each milestone ends with a green `lake build` and a commit.

1. **Semantics harness.** Lemmas for running small hand-written CakeML programs under
   `evaluate`/`evaluateDecs`/`semanticsProg` from `primSemEnv`: clock
   monotonicity, determinism, and how evaluating a terminating program yields
   `semanticsProg … (.terminate …)` and excludes other behaviours. Acceptance:
   `Implements`-style theorem for a toy program (e.g. one that always writes `accepted\n`
   and ignores its input relative to a toy reference).
2. **Refinement core.** Refinement invariants (`NAT`, `INT`, `BOOL`, `LIST a`,
   `OPTION a`, user inductives) and the `Eval env exp P` judgement with the
   translator's combinator lemmas (app, let, if, match, closures, letrec).
   Acceptance: hand-applied certificates for `List.length`, `List.append`, a
   `Nat` recursion.
3. **Translator automation.** A Lean metaprogram: given a Lean definition (structural or
   well-founded recursion, matches on inductives, the supported base types), emit the
   CakeML declarations and prove their certificate. Datatype translation for
   inductive types. Acceptance: automatic translation of a few hundred lines of
   representative con-leche-style code.
4. **Runtime types.** CakeML representations and refinement lemmas for `Array`, `ByteArray`,
   `UInt8`/`UInt32`/`UInt64`/`USize`, `Char`, `String`, `Std.HashMap`
   (and whatever else con-leche's checker reaches). Pure persistent versions first;
   mutable-array versions (monadic translation) only if needed for performance.
5. **I/O wrapper.** A hand-proved CakeML main: read all input via `read`, call the
   translated pipeline, write the verdict via `write`. Prove `Implements` from the
   pipeline's certificate. Acceptance: `Implements` holds for a program whose
   pipeline is a translated toy checker.
6. **Translate con-leche.** Translate the reference pipeline: `builtinPreludeE`,
   `parseChunks`, `preparePrelude`, `checkDecls`, `natOpPinSets` (the embedded
   pin data). For `partial`/`unsafe`/`implemented_by` definitions, translate the
   logical definition, adapting via proved-equal rewrites where needed.
   `@[computed_field]` fields are recomputed functions in CakeML.
7. **Final theorem.** `conPastel_correct : Implements conPastelProg`, axioms audit, and
   a README describing the statement and its assumptions.

Optional after the goal: run the program (via flapjack's `cake` or the
original CakeML compiler) on con-leche's test fixtures to compare verdicts and measure
performance.
