import ConPastel.Leche.Datatypes
import ConPastel.Leche.Blobs0
import ConPastel.Leche.Blobs1
import ConPastel.Leche.Blobs2
import ConPastel.Leche.Blobs3

/-!
# Checker stage, part: pin variants 2 and 3 (`natOpPinSet_v2`, `natOpPinSet_v3`)

An independent module (`cake_module`) over the shared datatypes, built in
parallel with the other parts; `ConPastel.Leche.Checker` imports every part
and reuses their units.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_module "CheckerPins23"
cake_unit ConLeche.natOpPinSet_v2 ConLeche.natOpPinSet_v3
end ConPastel.Leche
