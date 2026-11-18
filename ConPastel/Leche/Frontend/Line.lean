import ConPastel.Leche.Frontend.IndDecl
import ConPastel.Leche.Frontend.DefQuot
import ConPastel.Leche.Frontend.MiscDecl

/-!
# Frontend stage, part: the export line scanner (`naiveLineLoop`)

An independent module (`cake_module`) over the shared datatypes, built in
parallel with the other parts; `ConPastel.Leche.Frontend` imports every part
and reuses their units.
It imports the line-parser parts, whose units it reuses.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_module "FrontendLine"
cake_unit ConLeche.Frontend.naiveLineLoop
end ConPastel.Leche
