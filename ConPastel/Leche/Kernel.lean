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
cake_mutual_prepare ConLeche.Cached.whnfCoreI ConLeche.Expr.beqMemo ConLeche.Expr.hasFvarFast
  ConLeche.Expr.looseBVarsBoundedFast ConPastel.Impl.mkBvarD
  ConPastel.Impl.instantiate1M ConPastel.Impl.instantiateLiftM ConPastel.Impl.liftLooseBVarsM
  ConPastel.Impl.abstract1M ConPastel.Impl.abstractRangeM ConPastel.Impl.instLevelParamsM
  ConPastel.Impl.instantiateListM ConPastel.Impl.instantiateRevM ConPastel.Impl.u64toBV
  (@ConPastel.Braun.arrSize ConLeche.Expr) (@ConPastel.Braun.arrPush ConLeche.Expr)
  (@ConPastel.Braun.arrGet ConLeche.Expr) (@ConPastel.Braun.A.toList ConLeche.Expr)
  (@BitVec.toNat 64) ConPastel.Impl.leanMixHashF (@List.instDecidableEqNil ConLeche.Level) Nat.ble
  UInt8.ofNat (@instDecidableEqList ConLeche.Name ConLeche.instDecidableEqName)
  ConPastel.Leche.StateRw.memoBIR ConPastel.Leche.StateRw.whnfCoreLookupIR ConPastel.Leche.StateRw.storeChainIR
  ConPastel.Leche.StateRw.instListMR ConPastel.Leche.StateRw.isEquivLMR ConPastel.Leche.StateRw.constTyAtMR
  ConPastel.Leche.StateRw.constValAtMR ConPastel.Leche.StateRw.ruleRhsAtMR ConPastel.Leche.StateRw.maxNatSizeMR
  (@ConPastel.Translator.getM ConLeche.Expr ConLeche.Expr ConLeche.CheckError _ _)
  (@ConPastel.Translator.insertM ConLeche.Expr ConLeche.Expr ConLeche.CheckError _ _)
  (@ConPastel.Leche.StateRw.withEagerMemosR Bool)
end ConPastel.Leche
