import ConPastel.Leche.Kernel
import ConPastel.Leche.Blobs0
import ConPastel.Leche.Blobs1
import ConPastel.Leche.Blobs2
import ConPastel.Leche.Blobs3

/-!
# Translation stage: the declaration checker

con-leche's declaration fold (`checkDecls`) at the shipped binary's mode,
pins and maximum Nat size, on top of the kernel stage. The pin variants'
`let`-chain blobs go through `decodeBlob` (`ConPastel.Leche.Blobs<i>`).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
open ConLeche ConLeche.Cached ConLeche.Frontend in
cake_unit (ConLeche.Cached.checkDecls .verified ConLeche.natOpPinSets ConLeche.Cached.maxNatSizeDefault)
end ConPastel.Leche
