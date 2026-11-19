import ConPastel.Leche.Datatypes
import ConPastel.Leche.Intern
import ConPastel.Leche.Frontend.IndDecl
import ConPastel.Leche.Frontend.DefQuot
import ConPastel.Leche.Frontend.MiscDecl
import ConPastel.Leche.Frontend.ApplyDecl
import ConPastel.Leche.Frontend.Entries
import ConPastel.Leche.Frontend.Prelude
import ConPastel.Leche.Frontend.Line

/-!
# Translation stage: the frontend

The built-in prelude, the export parser (`parseChunks`) and the prelude
preparation (`preparePrelude`), on top of the kernel stage and the shared
datatypes (`ConPastel.Leche.Datatypes`); built in parallel with the checker.
Its largest subtrees are translated first, in parallel, by the independent
modules `ConPastel.Leche.Frontend.*`; this module reuses their units.
-/

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.all false
set_option maxRecDepth 200000

namespace ConPastel.Leche
cake_module "Frontend"
-- the export is parsed with interning (`ConPastel.Leche.Intern`)
cake_replace ConLeche.Frontend.parseChunks ConPastel.Impl.parseChunksI ConPastel.Impl.parseChunks_eq_I
cake_unit ConLeche.Frontend.builtinPreludeE ConPastel.Impl.parseChunksI ConLeche.Frontend.preparePrelude
end ConPastel.Leche
