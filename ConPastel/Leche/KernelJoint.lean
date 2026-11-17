import ConPastel.Leche.KernelPart0
import ConPastel.Leche.KernelPart1
import ConPastel.Leche.KernelPart2
import ConPastel.Leche.KernelPart3
import ConPastel.Leche.KernelPart4
import ConPastel.Leche.KernelPart5
import ConPastel.Leche.KernelPart6
import ConPastel.Leche.KernelPart7
import ConPastel.Leche.KernelPart8
import ConPastel.Leche.KernelPart9
import ConPastel.Leche.KernelPart10
import ConPastel.Leche.KernelPart11

/-! Translation stage: the kernel's mutual block, assembled from its parts
(see `ConPastel.Leche.Kernel`): the joint well-founded induction and the
members' certificates. -/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_mutual_finish ConLeche.Cached.whnfCoreI
end ConPastel.Leche
