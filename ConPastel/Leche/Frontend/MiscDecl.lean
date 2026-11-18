import ConPastel.Leche.Datatypes

/-!
# Frontend stage, part: the string, opaque, axiom and theorem line parsers

An independent module (`cake_module`) over the shared datatypes, built in
parallel with the other parts; `ConPastel.Leche.Frontend` imports every part
and reuses their units.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_module "FrontendMiscDecl"
cake_unit ConLeche.Frontend.naiveStrName ConLeche.Frontend.naiveStr ConLeche.Frontend.naiveOpaqueDecl ConLeche.Frontend.naiveAxiomDecl ConLeche.Frontend.naiveThmDecl
end ConPastel.Leche
