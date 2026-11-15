import ConPastel.Leche.Checker

/-!
# Translation stage: the frontend

The built-in prelude, the export parser (`parseChunks`) and the prelude
preparation (`preparePrelude`), on top of the checker stage.
-/

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.all false
set_option maxRecDepth 200000

namespace ConPastel.Leche
cake_unit ConLeche.Frontend.builtinPreludeE ConLeche.Frontend.parseChunks ConLeche.Frontend.preparePrelude
end ConPastel.Leche
