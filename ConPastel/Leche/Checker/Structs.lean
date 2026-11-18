import ConPastel.Leche.Datatypes
import ConPastel.Leche.Blobs0
import ConPastel.Leche.Blobs1
import ConPastel.Leche.Blobs2
import ConPastel.Leche.Blobs3

/-!
# Checker stage, part: structure projections, `Expr` instantiation and the basis checks

An independent module (`cake_module`) over the shared datatypes, built in
parallel with the other parts; `ConPastel.Leche.Checker` imports every part
and reuses their units.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_module "CheckerStructs"
cake_unit ConLeche.Cached.structProjBodiesC ConLeche.Expr.instantiateLiftP ConLeche.basisNamesOk ConLeche.Cached.blockConstantsC ConLeche.mkFEnv ConLeche.pinListOk ConLeche.Cached.checkQuotRecordC
end ConPastel.Leche
