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

## 3. FFI surface (new oracle calls)

| call | caller | conf / buffer | result |
|---|---|---|---|
| `spawn` | phase 1 end | conf: `K`, `N` | buffer byte: `0` parent, `1` worker |
| `claim` | worker | — | next index (e.g. 8 bytes little-endian) or a `done` flag |
| `report` | worker | conf: `k`, result code | — |
| `collect` | parent | buffer of `K` result bytes | table filled; per-child status |

In the per-process semantics these answers are arbitrary oracle data.
Extend the FFI model in `ConPastel/Spec.lean` (`Stdio`, `stdioOracle`) to a
parallel oracle whose answers to the new calls are unconstrained, or come from
an oracle script per process.

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

Pancake was considered. It has no atomics and makes syscalls only through FFI
stubs in C, and there is no Pancake semantics in Lean, so it would neither
shrink the trusted part nor enter the theorem. Keep the claim loop and the
verdict walk inside the proved CakeML program instead.

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
