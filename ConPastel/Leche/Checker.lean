import ConPastel.Leche.Kernel

/-!
# Translation stage: the declaration checker

con-leche's declaration fold (`checkDecls`) at the shipped binary's mode,
pins and maximum Nat size, on top of the kernel stage.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
open ConLeche ConLeche.Cached ConLeche.Frontend in
cake_unit (ConLeche.Cached.checkDecls .verified ConLeche.natOpPinSets ConLeche.Cached.maxNatSizeDefault)
end ConPastel.Leche
