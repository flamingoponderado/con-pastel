import ConPastel.Leche.Jobs
import ConPastel.Par.Final
import ConPastel.Program.Command

/-!
# The parallel checker's program and its per-process theorem

`parProg` is the CakeML program of the parallel mode (`--jobs=N`, `docs/PARALLEL-PLAN.md`): the
translated units of the jobs (`ConPastel.Leche.Jobs`) and the parallel main declarations
(`ConPastel.Par.parMainDecs`). `par_process`: for every script of FFI answers, one process of it
terminates and its events satisfy `ProcOk` (`ConPastel.Par.ParProcess`).

This module is not imported by `ConPastel.Leche.Program`: the default program `conPastelProg` and
`conPastel_correct` are unchanged.
-/

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.all false
set_option maxRecDepth 200000

namespace ConPastel

cake_program_par parP ConPastel.Par.phase1 ConPastel.Par.phase1Ok ConPastel.Par.jobCode ConPastel.Par.verdictCode

/-- The parallel checker's program. -/
noncomputable def parProg : List Flapjack.AstHOL.Dec := parP.prog

/-- **One process of the parallel checker is correct**, for every script of FFI answers. -/
theorem par_process (h : RuntimeAssumptions) : Par.ParProcess parProg := parP.correct h

#print axioms par_process

/-- **The parallel checker's correctness**: under the runtime assumptions and the harness
assumptions (`ConPastel.Par.HarnessRun`), the parent process writes con-leche's verdict. -/
theorem par_correct (h : RuntimeAssumptions) : Par.ParImplements parProg :=
  Par.parImplements_of_process (par_process h)

#print axioms par_correct

end ConPastel
