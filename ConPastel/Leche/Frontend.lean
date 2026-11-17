import ConPastel.Leche.Datatypes

/-!
# Translation stage: the frontend

The built-in prelude, the export parser (`parseChunks`) and the prelude
preparation (`preparePrelude`), on top of the kernel stage and the shared
datatypes (`ConPastel.Leche.Datatypes`); built in parallel with the checker.
-/

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.all false
set_option maxRecDepth 200000

namespace ConPastel.Leche
cake_module "Frontend"
cake_unit ConLeche.Frontend.builtinPreludeE ConLeche.Frontend.parseChunks ConLeche.Frontend.preparePrelude
end ConPastel.Leche
