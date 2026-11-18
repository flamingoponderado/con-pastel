import ConPastel.Leche.Datatypes
import ConPastel.Leche.Checker.Pins01
import ConPastel.Leche.Checker.Pins23
import ConPastel.Leche.Checker.Positivity
import ConPastel.Leche.Checker.NestSeeds
import ConPastel.Leche.Checker.Classes
import ConPastel.Leche.Checker.GenRec
import ConPastel.Leche.Checker.Tables
import ConPastel.Leche.Checker.Structs
import ConPastel.Leche.Blobs0
import ConPastel.Leche.Blobs1
import ConPastel.Leche.Blobs2
import ConPastel.Leche.Blobs3

/-!
# Translation stage: the declaration checker

con-leche's declaration fold (`checkDecls`) at the shipped binary's mode,
pins and maximum Nat size, on top of the kernel stage and the shared
datatypes (`ConPastel.Leche.Datatypes`); built in parallel with the frontend.
Its largest subtrees are translated first, in parallel, by the independent
modules `ConPastel.Leche.Checker.*`; this module reuses their units. The pin variants'
`let`-chain blobs go through `decodeBlob` (`ConPastel.Leche.Blobs<i>`).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_module "Checker"
open ConLeche ConLeche.Cached ConLeche.Frontend in
cake_unit (ConLeche.Cached.checkDecls .verified ConLeche.natOpPinSets ConLeche.Cached.maxNatSizeDefault)
end ConPastel.Leche
