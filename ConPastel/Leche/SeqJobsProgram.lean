import ConPastel.Leche.Jobs
import ConPastel.Leche.Program

/-!
# The in-order jobs program and its correctness

The same statement as `conPastel_correct`, for a second CakeML program whose entry runs the first
phase (parse, prepare, `buildIndex`) and then every record's job (`recordJob`) in order, deciding
by the first job that fails (`ConPastel.Par.seqEntry`). It is the parallel mode on one process,
with no FFI call beyond `read` and `write`: it validates the translation of the jobs, and its
verdicts can be compared with the default program's.

The default program, `conPastelProg`, is assembled in `ConPastel.Leche.Program` without these units
and is unchanged.
-/

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.all false
set_option maxRecDepth 200000

namespace ConPastel

/-- The in-order jobs checker on the values of the input bytes. -/
def seqJobsEntry (bs : List Nat) : Bool := Par.seqEntry bs

cake_unit seqJobsEntry
cake_program seqJobsP seqJobsEntry

/-- The in-order jobs program. -/
noncomputable def seqJobsProg : List Flapjack.AstHOL.Dec := seqJobsP.prog

theorem par_entryOf : Par.entryOf = entryOf := rfl

/-- **The in-order jobs program's correctness**, the same statement as `conPastel_correct`. -/
theorem seqJobs_correct (h : RuntimeAssumptions) : Implements seqJobsProg :=
  implementsRef_of_completes _ _ fun input => by
    obtain ⟨events, hc, hw⟩ := seqJobsP.correct h input
    exact ⟨events, hc, by rw [hw, seqJobsEntry, Par.seqEntry_eq, par_entryOf, entryOf_input]⟩

#print axioms seqJobs_correct

end ConPastel
