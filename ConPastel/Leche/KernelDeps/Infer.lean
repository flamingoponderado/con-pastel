import ConPastel.Leche.Sharing

/-!
# Kernel dependencies, part: projection types, free-variable leaves and binder residuals

An independent module (`cake_module`) over the shared datatypes
(`ConPastel.Leche.KernelTypes`), built in parallel with the other parts;
`ConPastel.Leche.KernelDeps` imports every part and reuses their units.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
cake_module "KernelDepsInfer"
cake_unit ConLeche.ProjEntry.typeAtI ConLeche.Expr.fvarLeavesC ConLeche.Cached.inferLamsOutI ConLeche.Cached.piResidualM
end ConPastel.Leche
