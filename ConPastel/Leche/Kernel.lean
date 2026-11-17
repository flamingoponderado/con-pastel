import ConPastel.Leche.KernelDeps

/-!
# Translation stage: the kernel's mutual block, prepared

con-leche's kernel core (`whnf`/`infer`/`defeq`/…): one mutual block of 69
functions, translated together with its joint correctness theorem. Its
dependencies come from `ConPastel.Leche.KernelDeps`.

The block is translated in several modules (`cake_mutual_prepare`), so that
Lake solves its members in parallel processes: this module prepares it,
`ConPastel.Leche.KernelPart0` … `KernelPart11` each solve every twelfth member,
and `ConPastel.Leche.KernelJoint` assembles the joint theorem.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
open ConLeche ConLeche.Cached ConLeche.Frontend in
-- the units after the block's name are needed by its members but not found by
-- the dependency pre-pass (each `cake_mutual_part` reports any that are missing)
cake_mutual_prepare ConLeche.Cached.whnfCoreI
  (@BitVec.toNat 64) ConPastel.leanMixHash (@List.instDecidableEqNil ConLeche.Level) Nat.ble
  UInt8.ofNat (@instDecidableEqList ConLeche.Name ConLeche.instDecidableEqName)
end ConPastel.Leche
