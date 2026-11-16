import ConPastel.Main.Code
import ConPastel.Spec

/-!
# Translation stage: the dependencies of the kernel's mutual block

con-leche's kernel core (`whnf`/`infer`/`defeq`/…) is one mutual block of 69
functions. This stage translates everything that block calls (not the block
itself), so that the stages translating the block start from these units.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche
-- con-leche's `@[computed_field]`s are stored in the CakeML constructors (as in
-- Lean's runtime): reading one is a projection, not a walk over the term
cake_cached ConLeche.Name ConLeche.Name.hashData
cake_cached ConLeche.Level ConLeche.Level.hashData
cake_cached ConLeche.Expr ConLeche.Expr.data
cake_prepass ConLeche.Cached.whnfCoreI
end ConPastel.Leche
