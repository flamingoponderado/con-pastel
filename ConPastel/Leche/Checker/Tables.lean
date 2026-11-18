import ConPastel.Leche.Datatypes
import ConPastel.Leche.Blobs0
import ConPastel.Leche.Blobs1
import ConPastel.Leche.Blobs2
import ConPastel.Leche.Blobs3

/-!
# Checker stage, part: the Nat division pin, recursor streams and block tables

An independent module (`cake_module`) over the shared datatypes, built in
parallel with the other parts; `ConPastel.Leche.Checker` imports every part
and reuses their units.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_module "CheckerTables"
cake_unit ConLeche.Cached.checkDivModPinC ConLeche.Cached.streamRecsCheckC ConLeche.Cached.blockTablesC
end ConPastel.Leche
