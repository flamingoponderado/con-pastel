# Parallel checking for con-pastel: plan

Goal: an **optional** `--jobs=N` mode that checks the declarations on N
**processes**, each running the same CakeML-compiled program. Without the flag
(or with `--jobs=1`) the program behaves exactly as today. `conPastel_correct`
stays as it is (axioms `[propext, Classical.choice, Quot.sound]` only), and the
parallel mode gets its own theorem stated under explicit harness assumptions.

The model is con-agua's (`leanprover/con-agua`, OVERVIEW.md §2.3 and §9):
a sequential first phase, then independent jobs claimed from a shared counter,
the verdict being that of the failing job with the smallest index. We use
processes instead of threads, because CakeML has no shared-memory threads.

## 1. The logical core already exists in con-leche

`deps/con-leche/ConLeche/Cached/StreamIndex.lean`:

```
recordJob mode pins maxNatSize I k pd : Except CheckError Unit
  -- record k, checked at the stream index's view of position k, from a FRESH state
```

`deps/con-leche/ConLeche/Verify/Cached/StreamIndex.lean`:

```
theorem checkDecls_of_jobs
    (h : ∀ k (hk : k < ds.size), recordJob mode pins maxNatSize (buildIndex ds) k ds[k] = .ok ()) :
    checkDecls mode pins maxNatSize ds = .ok (streamEnv ds.toList)
```

Each job starts from a fresh state, so jobs can run in any order on any
process. Unlike con-agua/con-ron, we do **not** need "each worker claims
increasing indices": no worker state carries across jobs.
con-leche's own driver (`ConLeche/Driver/CheckPool.lean`) uses exactly this
decomposition with threads; read it for the job granularity: one job per
claim, because heavy declarations cluster in the stream.

## 2. Architecture: fork after the first phase

One CakeML program:

1. **Phase 1, sequential, in one process**: read the input, parse, prepare
   the prelude, `buildIndex ds`. This yields `ds`, `I`, `K = ds.size`.
2. **`spawn` (FFI)**: the harness forks N workers. Each child inherits the
   CakeML heap copy-on-write, so `ds` and `I` need no serialization
   (con-agua's frozen buffer, `par_compact`, is not needed).
3. **Workers** loop: `claim` (FFI) returns the next index `k` or `done`; run
   `recordJob … I k ds[k]`; `report(k, code)` (FFI); repeat. When `done`, the
   worker ends normally.
4. **Parent**: `collect` (FFI) waits for every child and returns the results
   table and the children's exit statuses. The parent's CakeML code (proved)
   walks `k = 0 … K-1`: the first entry that is not `ok` decides (reject or
   decline by its code); all `ok` means accept. A missing or garbled entry, or a
   child that crashed (CakeML heap exhausted, OOM, signal), is **never** an
   accept: report an error/decline exit code.

### Keep the GC-managed area and the communication buffers separate

This is the most important design rule.

- The CakeML heap is private to each process after `fork` (copy-on-write).
  Nothing is ever shared *through* it.
- The shared state is a `mmap(MAP_SHARED | MAP_ANONYMOUS)` region created
  by the harness at `spawn`, **outside** the CakeML heap and stack: the claim
  counter, the results array (one entry per job), and optionally per-child
  status words.
- The input bytes are already read in phase 1; workers do not touch the
  input buffer again. If the input buffer is shared at all, it is read-only
  and outside the heap.
- CakeML code touches the shared region **only** through FFI calls, which
  copy bytes between the shared region and a CakeML byte array (as `read` and
  `write` do today). The FFI model then stays a pure oracle per process, and no
  CakeML value ever lives in shared memory.

### The FFI contract

The design stays inside CakeML's FFI model:

- An FFI call may change only the bytes of the byte array it is passed (keeping
  its length) and the abstract oracle state. It must not write the CakeML heap,
  stack or registers in any other way.
- So the shared memory stays outside the CakeML heap, is only copied in or out
  by FFI calls, and no pointer is ever passed back to CakeML.
- `fork` is fine as an FFI call: in each process, memory is unchanged except
  the array, and the parent/worker answer is ordinary oracle nondeterminism.
- Workers never write to stdout; only the parent writes the verdict.
  `ffiwrite` already flushes on every write, but the harness also checks that
  no buffered output exists at `fork` time (it flushes stdout and stderr in
  `spawn`, before forking).

## 3. FFI surface (new oracle calls)

The translator has no CakeML strings as values, so CakeML never encodes a
number into an FFI configuration. Numbers travel in the 9-byte job buffer
`jb` instead, and the harness never needs `K`:

| call | caller | conf | buffer | effect |
|---|---|---|---|---|
| `spawn` | after phase 1 | `""` | `jb` | forks the workers; `jb[0] = 0` in the parent, `1` in a worker |
| `claim` | worker | `""` | `jb` | `jb[1..8]` = the next index `k`, little-endian |
| `report` | worker | `"1"`, `"2"` or `"3"` | `jb` (still holding `k`) | records the code of job `k` |
| `results` | parent | `""` | `buf` (2 bytes) | the table, one entry per call, with `read`'s protocol |
| `abort` | parent | `""` | `buf` | the harness exits with code 3 |

* Job codes (`ConPastel/Par/Entry.lean`, `runJob`): `1` the job passes,
  `2` it fails, `3` there is no job `k` (`k ≥ K`). A worker loops
  `claim`, `report` until it reports `3`, then ends.
* The harness serves `results` only after every worker exited with status 0
  (else it exits with code 3), and serves the table entries `1`/`2` in index
  order up to the first `3` (an entry never reported makes it exit with code 3).
* The parent decides with `verdictCode` on the list it read: `0` writes
  `accepted`, `1` writes `rejected`, `2` (not a table of its jobs: wrong
  length, or a code other than `1`/`2`) calls `abort`.
* If phase 1 fails (the input does not parse), the parent writes `rejected`
  without spawning.

In the per-process semantics these answers are oracle data. The FFI model
(`ParIO`) is a script per process: the input, the `spawn` answer, the list of
`claim` answers, and the table `results` serves. A process's actual run is its
run under the script of the answers it actually got, so a theorem for every
script covers every harness behaviour. Running out of `claim` answers is an
FFI failure (`.final`), as is `abort`.

## 4. Proof plan

1. **Reject direction, pure Lean (new).** Our final theorem is an exact
   boolean (`accepted` iff `conLecheAccepts`), so rejects must be justified too.
   Prove: if every `j < k` has `recordJob … (buildIndex ds) j ds[j] = .ok ()`
   and job `k` fails, then `checkDecls … ds` is an error. Use `jobs_run`
   (prefix up to `k`), `viewTwin`/`view_eq` (the view at `k` is the fold's
   environment there) and `declStep` (same `checkDeclStepC`, same fresh
   state). Check `andPinOk` on both sides.
2. **Per-process theorem (CakeML level), for every oracle answer to the new calls:**
   - a run that calls `report(k, ok)` has `k < K` and
     `recordJob … (buildIndex ds) k ds[k] = .ok ()`, with `ds` from the input
     bytes that run read;
   - the parent writes `accepted` only if the table it got says `ok` for every
     `k < K`;
   - it writes `rejected` only if, at the smallest non-`ok` index, the table
     holds a failure code and every smaller index is `ok`.
3. **Harness assumptions** (stated, not proved; cf. con-agua's `ThreadsRun`,
   `ConAgua/Final/ThreadsFinal.lean`):
   - every process read the same input bytes;
   - every entry for index `k` in the parent's table was produced by a
     `report(k, …)` call of some process whose run is a run of the same program
     on the same input, with `spawn` answering "worker";
   - nothing else writes the table.
4. **Composition.**
   - Accept: steps 2 and 3, then `checkDecls_of_jobs`, give `conLecheAccepts`.
   - Reject: step 1 gives `¬ conLecheAccepts`.
   - State it as a new `ParImplements` theorem next to `Implements`.
     `--jobs=1` keeps the current program path and `conPastel_correct` untouched.

## 5. Harness

Thin C stubs next to `release/con_pastel_ffi.c` (about 100 lines):
`mmap(MAP_SHARED|MAP_ANONYMOUS)`, `fork`, `__atomic_fetch_add` for `claim`, a
store for `report`, `waitpid` for `collect`, and `--jobs=N` parsing in `main`.

Pancake was considered. flapjack does port Pancake to Lean
(`deps/flapjack/Flapjack/Pancake`: `PanLang`, its semantics, `PanToTarget`
and the passes below it), but Pancake has no atomics and makes syscalls only
through FFI, so the C stubs for `fork`, `mmap`, the atomic add and `waitpid`
stay either way. For now the claim loop and the verdict walk stay inside the
proved CakeML program. If harness logic beyond those stubs is ever written,
Pancake with a Lean proof is an option for it.

## 6. Practical risks (check early)

- **Heap per worker.** The CakeML heap is fixed in size, with a copying GC,
  and the runtime touches the whole heap before its first collection
  (`release/con_pastel_ffi.c`, default 4 GiB). N workers can reach N × heap in
  RSS. Size the heap by `--jobs` (e.g. `CML_HEAP_SIZE`), and measure.
- **Transparent huge pages and copy-on-write.** The runtime does
  `madvise(MADV_HUGEPAGE)`. After `fork`, each write to a shared huge page
  copies 2 MB. Use `MADV_NOHUGEPAGE` in parallel mode, or advise again before
  `fork`.
- **Translation.** `buildIndex`, `recordJob`, `StreamIndex.view` are not
  translated today: the current program uses `checkDecls`/`declStep`
  (`ConPastel/Leche/Checker.lean`, `KernelTypes.lean`: `declStep` is replaced
  by `declStepR` through `runRef`, and `recordJob` will need the same
  `runRef`-style treatment, since `checkDeclStepC` runs in the state monad).
- **Amdahl.** Phase 1 stays sequential.

## 7. Milestones

1. The reject-direction lemma (pure Lean).
2. Translate `buildIndex` and `recordJob`. Build a sequential entry
   "phase 1, then jobs 0 … K-1 in order", proved under the existing
   `Implements`. This validates the translation and the lemma before any FFI
   work, and can be compared against the current path on the fixture suite.
3. The FFI model for the new calls, and the per-process theorem.
4. The C stubs, `--jobs=N` in `release/`, and the parent verdict walk.
5. The `ParImplements` statement with documented assumptions.
6. Tuning (heap per worker, THP), and benchmarks: `release/test.sh` with and
   without `--jobs`, and the large fixtures.

## 8. Status and changes to the design

**Changes made while implementing.**

* **A separate executable.** CakeML compiles one program per executable, and
  the default program's FFI model has only `read` and `write`, so the
  parallel mode is `release/build/con-pastel-par [--jobs=N]` (default 1
  worker), built from its own program `parProg` (`make -C release par`).
  `release/build/con-pastel`, `conPastelProg` and `conPastel_correct` are
  unchanged.
* **No numbers in CakeML strings** (§3): `spawn` does not get `K`; workers
  report code 3 past the last job, and the parent reads the table with
  `read`'s protocol.
* **One FFI model per process with a script** (`ConPastel/Par/Spec.lean`),
  and the per-process theorem states exactly what each process does
  (`ProcOk`), rather than only "a report of ok".
* `cake_program` assembles every unit in scope, so the jobs' units live in
  modules the default program does not import (`ConPastel.Leche.Jobs`,
  `SeqJobsProgram`, `ParProgram`), and their datatypes are registered in
  `Jobs` before its `cake_module` tag.

**Milestones.**

1. Done: `checkDecls_error_of_jobs`, `walkJobs_eq` (`ConPastel/Par/Jobs.lean`).
2. Done: `seqJobs_correct : Implements seqJobsProg`; on the fixture suite
   `con-pastel-seqjobs` gives `pass=553 fail=8`, the same 8 known failures
   as the default program.
3. Done: `parOracle`, `par_process : ParProcess parProg`.
4. Done: `con_pastel_par_ffi.c`, `--jobs=N`, the parent's verdict walk
   (`verdictCode`, proved).
5. Done: `par_correct : ParImplements parProg` under `HarnessRun`.
   The assumptions are listed in `docs/SOUNDNESS.md` (items 16 to 21).
6. In progress: measurements (heap per worker, THP, speed-up).

**Files.** `ConPastel/Par/`: `Jobs` (the decomposition), `Entry` (phase 1,
job codes, verdict), `Spec` (FFI model), `Code` (main declarations),
`Ffi`, `Work`, `Main`, `Run`, `Decls`, `Assemble` (per-process proof),
`Final` (composition). `ConPastel/Leche/`: `Jobs`, `SeqJobsProgram`,
`ParProgram`. `release/`: `con_pastel_par_ffi.c`, `EmitPar.lean`,
`EmitSeqJobs.lean`.

## Working notes for this repository

- **Repository rules.**
  - The repo is public: never push to `main`; work on a branch and open a PR.
  - Commit messages end with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
  - PR bodies end with `🤖 Generated with [Claude Code](https://claude.com/claude-code)`.
- **Proofs.**
  - Never use `bv_decide` in translated proofs: it adds native axioms to `conPastel_correct`.
  - Check `#print axioms conPastel_correct` in the build log.
- **Builds.**
  - A full build takes about 25 minutes, and kernel modules use 5–14 GB each.
  - Another session builds in `../con-pastel-split`. Do not run two full lake builds at once on this machine: check `pgrep -fa "lake build"` first and wait.
  - Lake may replay modules from `~/.cache/lake-artifact-cache` without writing the `.olean` files, so `make` in `release/` then fails with "object file … does not exist". In that case, restore the outputs named in each module's `.trace` (`outputs` {o, i, c}) from the cache before `make`.
  - Release build: `cd release && rm -f build/con-pastel.sexp build/con-pastel.S && make`, which takes about 13 minutes of `cake`.
  - Fixture suite: `release/test.sh BIN 1000000 120`. The expected result today is `pass=553 fail=8`; the 8 known failures are `nat_size_ok`, five `nat_size_limit_*`, `natmul_deep_major` and `prop_struct_proj_wide`.
- **Hygiene.**
  - Kill processes by PID, never by pattern.
  - Never use bare `git stash`.
  - Keep scratch files small: `/tmp` is a shared tmpfs.
