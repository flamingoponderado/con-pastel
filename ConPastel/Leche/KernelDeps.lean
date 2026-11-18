import ConPastel.Leche.KernelTypes
import ConPastel.Leche.KernelDeps.Level
import ConPastel.Leche.KernelDeps.Shapes
import ConPastel.Leche.KernelDeps.Guards
import ConPastel.Leche.KernelDeps.Inst
import ConPastel.Leche.KernelDeps.Infer
import ConPastel.Leche.KernelDeps.Unfold
import ConPastel.Leche.KernelDeps.Abstract

/-!
# Translation stage: the dependencies of the kernel's mutual block

con-leche's kernel core (`whnf`/`infer`/`defeq`/…) is one mutual block of 69
functions. This stage translates everything that block calls (not the block
itself), so that the stages translating the block start from these units.
The largest subtrees are translated first, in parallel, by the independent
modules `ConPastel.Leche.KernelDeps.*`; the pre-pass here reuses their units
and translates the rest.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_prepass ConLeche.Cached.whnfCoreI
end ConPastel.Leche
