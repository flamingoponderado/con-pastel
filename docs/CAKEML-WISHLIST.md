# CakeML wishlist

What con-pastel would gain from changes to CakeML (the compiler, its
runtime or its source semantics), with the measurements behind each item.
The translated program is unchanged by all of these; they would speed up
the code cake generates from it. Numbers are user time on con-leche's
end-to-end fixtures, against `con-leche --jobs=1` on the same machine.

## 1. A working generational collector

cake v3479's `--gc=genN` stops with "heap exhausted" (exit 1) even on a
trivial non-tail recursion:

```sml
fun f n = if n = 0 then [] else n :: f (n-1);
val _ = print (Int.toString (List.length (f 10)) ^ "\n");
```

compiled with `cake --gc=gen1000` (also `gen10`, `gen10000000`) and linked
with cake's own `basis_ffi.c`. Tail-recursive loops, refs, arrays, bignums
and byte arrays all work under it.

Why it matters: with the simple Cheney collector every collection copies the
whole live set. `natmul_deep_major` keeps about 1.6 GB live (cached
expression nodes); with a 4 GiB heap, 87 collections took 63 s of a 74 s run
(con-leche: 4.3 s). The 8 GiB default (#61) brings it to 26 s, at the price
of memory. A generational collector would copy the old nodes once.

## 2. Unboxed 64-bit words in data

A `word64` value is a boxed heap object (header + word); so is every
intermediate result of word arithmetic. Each expression node stores its
packed data word boxed (2 extra words and one extra object per node), and a
hash computation allocates a box per operation. In `natop_perturbed_used_later`
21% of the words allocated before the first collection (mostly while parsing
the input) are boxed words; in the live heap of `natmul_deep_major`, 17.5 M of
the 57 M objects are boxed data words.

Wished: words stored unboxed in constructor fields (e.g. a header bit
marking raw fields), or unboxed word arithmetic within a function body when
the intermediate results do not escape.

## 3. Word multiplication

`wordArith` has `add`, `sub`, `and`, `or`, `xor` only. con-leche's hashes
(`mixHash`, MurmurHash64A) multiply 64-bit words; the translation does it on
22-bit limbs with small-integer multiplications (`mulL`, `mulMix`), about
twenty boxed operations per product. Hashing is about 20% of `letfold_let`
and 11% of `eager_open_nat_control`. A native `Arith Mul (WordT W64)` (and
`Div`/`Mod`) would make each product one instruction.

## 4. Word comparison

`Test` supports word8 only (`doTest`). 64-bit comparisons go through
conversions to integers, which are bignums when the top bits are set.

## 5. Evaluated top-level constants without closures

0-ary functions in a `Dletrec` are re-evaluated at each use. con-pastel's
proofs assemble the program from `Dletrec` groups, so its constants
(con-leche's names, levels and expression templates) are thunks: `natName`
(`Nat`) is rebuilt, string included, at every use. #62 folds their hashes;
the nodes are still rebuilt. A `Dlet` of a closed constructor term is the
CakeML-side answer, but it needs store-independent value bindings in the
proof framework; a compiler pass that hoists closed constructor terms (with
no refs) out of functions into static data would need nothing from the
proofs.

## 6. Pointer equality

CakeML's `=` on two constructor values compares structurally. The
translation gives every expression node a fresh reference (an identity
token) so that `=` returns at once on separate nodes: 2 words and one object
per node, and a field compared before the children. A physical equality
test on immutable blocks (sound to expose as "`true` implies equal") would
make the token unnecessary.

## 7. Sampling-friendly profiling

The numbers here come from gdb: a PC or stack sample every few milliseconds
(`SIGUSR1`), and breakpoints on `cml__GC`. `perf` is often unavailable
(`perf_event_paranoid`), and stack samples are biased (a deep stack takes
long to dump). Frame pointers or a documented frame layout, so that a
standard profiler can unwind CakeML stacks, would make profiling routine.

## 8. Collector statistics

No way to ask the runtime how much it collected or how often: the numbers
above come from gdb breakpoints on the generated `cml__GC` routine. A
`CML_GC_STATS`-style report at exit (number of collections, time, live
sizes) would make this measurable without a debugger.
