import ConPastel.Leche.Datatypes
import ConPastel.Leche.Blobs0
import ConPastel.Leche.Blobs1
import ConPastel.Leche.Blobs2
import ConPastel.Leche.Blobs3

/-!
# Checker stage, part: pin variants 0 and 1 (`natOpPinSet_v0`, `natOpPinSet_v1`)

An independent module (`cake_module`) over the shared datatypes, built in
parallel with the other parts; `ConPastel.Leche.Checker` imports every part
and reuses their units.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_module "CheckerPins01"
cake_unit ConLeche.natOpPinSet_v0 ConLeche.natOpPinSet_v1
end ConPastel.Leche
