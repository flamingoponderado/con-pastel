/*
  The FFI and runtime entry point for con-pastel's CakeML program.

  This file is TRUSTED: it must implement the FFI model that con-pastel's
  correctness theorem is stated against (`ConPastel.stdioOracle` in
  ConPastel/Spec.lean):

  * `read`, buffer `a` of at least 2 bytes: if input remains, set a[0] = 1
    and a[1] = the next input byte; at the end of the input set a[0] = 0.
    The rest of the buffer is unchanged.
  * `write`: the bytes to write are the configuration `c[0..clen)`; they are
    written to standard output. The buffer is unchanged.
  * any other FFI call, or `read` with a buffer shorter than 2 bytes, is an
    FFI failure: the process stops with exit code 4.

  The program only calls `read` and `write`. The runtime part (heap/stack
  allocation, here mapped on huge pages, `cml_exit`, `cml_err`, `main`) follows CakeML's basis_ffi.c
  (CakeML release v3479), without the basis library's FFI functions.
*/
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <string.h>
#include <unistd.h>

/* exported by the CakeML-generated assembly */
extern void cml_main(void);
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;
extern char cake_codebuffer_begin;
extern char cake_codebuffer_end;

static void ffi_failure(const char *what) {
  fflush(stdout);
  fprintf(stderr, "con-pastel: FFI failure (%s)\n", what);
  exit(4);
}

void ffiread(unsigned char *c, long clen, unsigned char *a, long alen) {
  (void)c; (void)clen;
  if (alen < 2) ffi_failure("read: buffer shorter than 2 bytes");
  int ch = getchar();
  if (ch == EOF) {
    if (ferror(stdin)) ffi_failure("read: input error");
    a[0] = 0;
  } else {
    a[0] = 1;
    a[1] = (unsigned char)ch;
  }
}

void ffiwrite(unsigned char *c, long clen, unsigned char *a, long alen) {
  (void)a; (void)alen;
  if (clen < 0) ffi_failure("write: negative length");
  if (clen > 0 && fwrite(c, 1, (size_t)clen, stdout) != (size_t)clen)
    ffi_failure("write: output error");
  if (fflush(stdout) != 0) ffi_failure("write: output error");
}

/* Called by the generated code when it stops early: 1 = heap exhausted,
   2 = stack exhausted. CakeML's compiler correctness theorem allows such an
   early stop; the output written so far is then a prefix of the specified
   output, and no verdict has been given. */
void cml_exit(int arg) {
  fflush(stdout);
  if (arg == 1) fprintf(stderr, "con-pastel: CakeML heap exhausted (set CML_HEAP_SIZE, in MiB)\n");
  else if (arg == 2) fprintf(stderr, "con-pastel: CakeML stack exhausted (set CML_STACK_SIZE, in MiB)\n");
  else if (arg != 0) fprintf(stderr, "con-pastel: CakeML program stopped with code %d\n", arg);
  exit(arg);
}

void cml_err(int arg) {
  if (arg == 3)
    fprintf(stderr, "con-pastel: memory not ready for entry\n");
  cml_exit(arg);
}

void cml_clear(void) {
  __builtin___clear_cache(&cake_codebuffer_begin, &cake_codebuffer_end);
}

#ifndef CON_PASTEL_HEAP_MIB
#define CON_PASTEL_HEAP_MIB 8192
#endif

static unsigned long env_mib(const char *name, unsigned long dflt) {
  const char *s = getenv(name);
  if (s == NULL) return dflt;
  char *end;
  unsigned long v = strtoul(s, &end, 10);
  if (*s == '\0' || *end != '\0') {
    fprintf(stderr, "con-pastel: %s must be a number of MiB\n", name);
    exit(3);
  }
  return v;
}

int main(int argc, char **argv) {
  (void)argc; (void)argv;
  const unsigned long mib = 1024UL * 1024UL;
  /* defaults: CON_PASTEL_HEAP_MIB heap (8 GiB), 4 GiB stack. The copying
     collector runs when a semispace is full, so a run touches as much of the
     heap as it allocates, up to all of it. The cost of a collection is the
     live data, and their number grows sharply as the live data approach the
     semispace: natmul_deep_major (1.6 GB live) spends 63 s of 74 s collecting
     with 4 GiB, and runs in 37 s with 8 GiB. Runs that allocate little are
     unaffected (the mapping is MAP_NORESERVE). */
  unsigned long heap_sz = env_mib("CML_HEAP_SIZE", CON_PASTEL_HEAP_MIB) * mib;
  unsigned long stack_sz = env_mib("CML_STACK_SIZE", 4096) * mib;
  if (heap_sz < mib || stack_sz < mib) {
    fprintf(stderr, "con-pastel: heap and stack must be at least 1 MiB each\n");
    exit(3);
  }
  /* Layout expected by CakeML: |--- heap ---||--- stack ---| */
  /* Mapped on a 2 MiB boundary and marked for transparent huge pages:
     the heap is touched for the first time as the program allocates, and
     with 4 KiB pages those first-touch faults dominate short runs. */
  const unsigned long huge = 2 * mib;
  unsigned long total = heap_sz + stack_sz;
  char *raw = mmap(NULL, total + huge, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (raw == MAP_FAILED) {
    perror("con-pastel: mmap");
    exit(3);
  }
  cml_heap = (void *)(((unsigned long)raw + huge - 1) & ~(huge - 1));
  madvise(cml_heap, total, MADV_HUGEPAGE);
  cml_stack = (char *)cml_heap + heap_sz;
  cml_stackend = (char *)cml_stack + stack_sz;
  cml_main();
  return 0;
}
