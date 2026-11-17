import ConPastel.Leche.Kernel

/-! Translation stage: members `i` of the kernel's mutual block with `i % 12 = 1`
(see `ConPastel.Leche.Kernel`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_mutual_part ConLeche.Cached.whnfCoreI 1 12
end ConPastel.Leche
