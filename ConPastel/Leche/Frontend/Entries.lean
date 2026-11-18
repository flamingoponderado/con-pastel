import ConPastel.Leche.Datatypes

/-!
# Frontend stage, part: the name, level and expression entry parsers

An independent module (`cake_module`) over the shared datatypes, built in
parallel with the other parts; `ConPastel.Leche.Frontend` imports every part
and reuses their units.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_module "FrontendEntries"
cake_unit ConLeche.Frontend.parseNameEntryD ConLeche.Frontend.parseLevelEntryD ConLeche.Frontend.parseExprEntryD
end ConPastel.Leche
