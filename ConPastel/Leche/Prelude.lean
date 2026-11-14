import ConPastel.Main.Code
import ConPastel.Spec

/-!
# Translation stage 1: the built-in prelude

The translation of con-leche is one linear chain of modules (units and
datatypes are registered in order); each stage translates a part of the
pipeline, and later stages reuse its units.
-/

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace ConPastel.Leche
cake_unit ConLeche.Frontend.builtinPreludeE
end ConPastel.Leche
