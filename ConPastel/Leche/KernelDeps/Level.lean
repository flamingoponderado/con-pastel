import ConPastel.Leche.Sharing

/-!
# Kernel dependencies, part: universe level comparison (`isEquivListLM`, `Level.leqCore`)

An independent module (`cake_module`) over the shared datatypes
(`ConPastel.Leche.KernelTypes`), built in parallel with the other parts;
`ConPastel.Leche.KernelDeps` imports every part and reuses their units.
`leanMixHash` comes first: `leqCore`'s mutual block needs it, and would
otherwise be solved twice (once to find it missing).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_module "KernelDepsLevel"
cake_unit ConPastel.Impl.leanMixHashF ConLeche.Level.leqCore ConLeche.Cached.isEquivListLM
end ConPastel.Leche
