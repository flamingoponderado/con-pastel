import ConPastel.Leche.Keys

/-!
# Frontend stage, part: the definition and quotient line parsers

An independent module (`cake_module`) over the shared datatypes, built in
parallel with the other parts; `ConPastel.Leche.Frontend` imports every part
and reuses their units.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_module "FrontendDefQuot"
cake_unit ConLeche.Frontend.naiveDefDecl ConLeche.Frontend.naiveQuotDecl
end ConPastel.Leche
