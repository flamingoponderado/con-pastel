import ConPastel.Leche.KernelTypes

/-!
# Kernel dependencies, part: unit-like shapes and projection guards

An independent module (`cake_module`) over the shared datatypes
(`ConPastel.Leche.KernelTypes`), built in parallel with the other parts;
`ConPastel.Leche.KernelDeps` imports every part and reuses their units.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_module "KernelDepsShapes"
cake_unit ConLeche.Cached.unitLikeShapeF ConLeche.projGuardRowsC
end ConPastel.Leche
