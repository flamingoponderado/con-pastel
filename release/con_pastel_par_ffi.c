/*
  The FFI and runtime entry point for con-pastel's PARALLEL program
  (`ConPastel.parProg`, docs/PARALLEL-PLAN.md).

  This file is TRUSTED. It implements, in each process, the FFI model that
  the per-process theorem `ConPastel.par_process` is stated against
  (`ConPastel.Par.parOracle` in ConPastel/Par/Spec.lean), and the harness
  assumptions under which the processes together give con-leche's verdict
  (`ConPastel.Par.HarnessRun`, ConPastel/Par/Final.lean).

  `read` and `write` are those of the default program (con_pastel_ffi.c,
  included below); in a worker, `write` is an FFI failure. The new calls:

  * `spawn`, buffer `jb` of 9 bytes: forks `--jobs` workers. In the parent
    jb[0] = 0, in each worker jb[0] = 1; the rest of `jb` is unchanged.
  * `claim`, buffer `jb` of 9 bytes: jb[1..8] = the next job index from the
    shared counter, little-endian. jb[0] is unchanged.
  * `report`, configuration "1", "2" or "3", buffer `jb` of 9 bytes: stores
    the code for the index in jb[1..8] in the shared table. Unchanged buffer.
  * `results`, buffer of at least 2 bytes, `read`'s protocol over the table:
    the first call waits for every worker and stops the process (exit 3) if
    one did not exit with status 0. Then it serves the codes 1/2 of jobs
    0, 1, ... and ends at the first code 3; a job never reported stops the
    process (exit 3).
  * `abort`: the process stops with exit code 3 (the table was not a table
    of the parent's jobs).

  The shared region (counter and table) is a MAP_SHARED anonymous mapping
  outside the CakeML heap and stack. CakeML touches it only through these
  calls, which copy bytes between it and the CakeML byte array they are
  given; no pointer is ever passed back to CakeML. Each process's CakeML heap
  is private after fork (copy-on-write).

  Exit codes: 0 with "accepted\n" or "rejected\n" on stdout (the verdict);
  3 for a harness error (a worker failed, the table is incomplete, abort);
  4 for an FFI failure; 1 and 2 for CakeML heap or stack exhaustion.
*/
#define main con_pastel_sequential_main
#define ffiwrite con_pastel_base_ffiwrite
#include "con_pastel_ffi.c"
#undef main
#undef ffiwrite

#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <sys/prctl.h>
#include <sys/types.h>
#include <sys/wait.h>

/* Table capacity: one byte per job index. Mapped with MAP_NORESERVE, so only
   the pages of indices actually reported use memory. */
#define TABLE_CAP (1UL << 32)

struct shared {
  uint64_t counter; /* next job index (atomic fetch-add) */
};

static long jobs = 1;
static int is_worker = 0;
static struct shared *shm = NULL;
static unsigned char *table = NULL;
static pid_t *children = NULL;
static long nchildren = 0;
static int results_ready = 0;
static uint64_t results_next = 0;

static void harness_error(const char *what) {
  fflush(stdout);
  fprintf(stderr, "con-pastel: parallel harness: %s\n", what);
  exit(3);
}

static uint64_t get_le64(const unsigned char *p) {
  uint64_t k = 0;
  for (int i = 7; i >= 0; i--) k = (k << 8) | p[i];
  return k;
}

static void put_le64(unsigned char *p, uint64_t k) {
  for (int i = 0; i < 8; i++) { p[i] = (unsigned char)(k & 0xff); k >>= 8; }
}

/* `write` in a worker is an FFI failure: only the parent writes the verdict. */
void ffiwrite(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (is_worker) ffi_failure("write: a worker never writes");
  con_pastel_base_ffiwrite(c, clen, a, alen);
}

void ffispawn(unsigned char *c, long clen, unsigned char *a, long alen) {
  (void)c; (void)clen;
  if (alen != 9) ffi_failure("spawn: buffer is not 9 bytes");
  if (shm != NULL || is_worker) ffi_failure("spawn: called twice");
  size_t sz = sizeof(struct shared) + TABLE_CAP;
  void *m = mmap(NULL, sz, PROT_READ | PROT_WRITE,
                 MAP_SHARED | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (m == MAP_FAILED) harness_error("mmap of the shared table failed");
  shm = (struct shared *)m;
  table = (unsigned char *)m + sizeof(struct shared);
  __atomic_store_n(&shm->counter, 0, __ATOMIC_SEQ_CST);
  children = calloc((size_t)jobs, sizeof(pid_t));
  if (children == NULL) harness_error("out of memory");
  /* no buffered output may be duplicated into the workers */
  if (fflush(stdout) != 0 || fflush(stderr) != 0) harness_error("flush before fork failed");
  /* The heap keeps its huge-page advice. After fork, a worker's copying GC
     writes into the whole heap, so it copies it on write; measured on
     init-prelude, MADV_NOHUGEPAGE here made that slower (1.05M faults,
     4.5 s) than keeping huge pages (742k faults, 4.0 s). The cost scales with
     CML_HEAP_SIZE. */
  pid_t parent = getpid();
  for (long i = 0; i < jobs; i++) {
    pid_t pid = fork();
    if (pid < 0) {
      for (long j = 0; j < nchildren; j++) kill(children[j], SIGKILL);
      harness_error("fork failed");
    }
    if (pid == 0) {
      /* a worker: stop if the parent goes away */
      prctl(PR_SET_PDEATHSIG, SIGKILL);
      if (getppid() != parent) _exit(3);
      is_worker = 1;
      a[0] = 1;
      return;
    }
    children[nchildren++] = pid;
  }
  a[0] = 0;
}

void fficlaim(unsigned char *c, long clen, unsigned char *a, long alen) {
  (void)c; (void)clen;
  if (alen != 9) ffi_failure("claim: buffer is not 9 bytes");
  if (!is_worker) ffi_failure("claim: not a worker");
  uint64_t k = __atomic_fetch_add(&shm->counter, 1, __ATOMIC_SEQ_CST);
  if (k >= TABLE_CAP) harness_error("too many jobs");
  put_le64(a + 1, k);
}

void ffireport(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (alen != 9) ffi_failure("report: buffer is not 9 bytes");
  if (!is_worker) ffi_failure("report: not a worker");
  if (clen != 1 || c[0] < '1' || c[0] > '3') ffi_failure("report: bad code");
  uint64_t k = get_le64(a + 1);
  if (k >= TABLE_CAP) ffi_failure("report: index out of range");
  __atomic_store_n(&table[k], (unsigned char)(c[0] - '0'), __ATOMIC_SEQ_CST);
}

static void wait_workers(void) {
  int failed = 0;
  for (long i = 0; i < nchildren; i++) {
    int st;
    pid_t r;
    do { r = waitpid(children[i], &st, 0); } while (r < 0 && errno == EINTR);
    if (r < 0) { failed = 1; continue; }
    if (WIFEXITED(st)) {
      if (WEXITSTATUS(st) != 0) {
        fprintf(stderr, "con-pastel: worker %ld exited with code %d\n", i, WEXITSTATUS(st));
        failed = 1;
      }
    } else if (WIFSIGNALED(st)) {
      fprintf(stderr, "con-pastel: worker %ld killed by signal %d\n", i, WTERMSIG(st));
      failed = 1;
    } else {
      failed = 1;
    }
  }
  if (failed) harness_error("a worker failed: no verdict");
}

void ffiresults(unsigned char *c, long clen, unsigned char *a, long alen) {
  (void)c; (void)clen;
  if (alen < 2) ffi_failure("results: buffer shorter than 2 bytes");
  if (is_worker || shm == NULL) ffi_failure("results: not the parent");
  if (!results_ready) {
    wait_workers();
    results_ready = 1;
  }
  if (results_next >= TABLE_CAP) harness_error("table overflow");
  unsigned char t = __atomic_load_n(&table[results_next], __ATOMIC_SEQ_CST);
  if (t == 3) {
    a[0] = 0;
  } else if (t == 1 || t == 2) {
    a[0] = 1;
    a[1] = t;
    results_next++;
  } else {
    harness_error("a job was never reported: no verdict");
  }
}

void ffiabort(unsigned char *c, long clen, unsigned char *a, long alen) {
  (void)c; (void)clen; (void)a; (void)alen;
  harness_error("the table is not a table of the parent's jobs: no verdict");
}

int main(int argc, char **argv) {
  for (int i = 1; i < argc; i++) {
    const char *s = argv[i];
    if (strncmp(s, "--jobs=", 7) == 0) {
      char *end;
      long n = strtol(s + 7, &end, 10);
      if (s[7] == '\0' || *end != '\0' || n < 1 || n > 4096) {
        fprintf(stderr, "con-pastel: --jobs=N needs 1 <= N <= 4096\n");
        exit(3);
      }
      jobs = n;
    } else {
      fprintf(stderr, "con-pastel: unknown argument %s (usage: con-pastel-par [--jobs=N] < export)\n", s);
      exit(3);
    }
  }
  return con_pastel_sequential_main(argc, argv);
}
