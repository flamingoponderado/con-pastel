import ConPastel.Leche.KernelDeps

/-!
# Translation stage: the kernel's mutual block

con-leche's kernel core (`whnf`/`infer`/`defeq`/…): one mutual block of 69
functions, translated together with its joint correctness theorem. Its
dependencies come from `ConPastel.Leche.KernelDeps`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
open ConLeche ConLeche.Cached ConLeche.Frontend in
cake_unit ConLeche.Cached.whnfCoreI
end ConPastel.Leche
