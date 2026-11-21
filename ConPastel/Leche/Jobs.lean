import ConPastel.Leche.Checker
import ConPastel.Leche.Frontend
import ConPastel.Par.Entry

/-!
# Translation stage: the jobs

The phases of the jobs-based checker (`ConPastel.Par.Entry`): the first phase (parse, prepare,
`buildIndex`), a job's code (`recordJob`), the verdict on a table of job codes, and the in-order
entry `seqEntry`. They reuse the checker's and the frontend's units.

This module is not imported by `ConPastel.Leche.Program`: `cake_program` assembles every unit in
scope, so the default program (`conPastelProg`) does not contain these units.

`recordJob` runs the record's check on a fresh state, as `declStep` does; it is replaced in the same
way (`declStepR`, `ConPastel.Leche.KernelTypes`) by the check run on a fresh reference (`runRef`).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.all false

namespace ConPastel.Leche

open ConLeche ConLeche.Cached in
/-- `recordJob`, the record's check run on a fresh reference (`runRef`). -/
def recordJobR (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat) (I : StreamIndex)
    (k : Nat) (pd : Declaration) : Except CheckError Unit :=
  if andPinOk pd then
    match ConPastel.Translator.runRef ({ maxNatSize := maxNatSize } : CState)
        (checkDeclStepC mode pins (I.view k) pd) with
    | .ok _ => .ok ()
    | .error e => .error e
  else .error (.invalid "`And` must be the standard `And`")

open ConLeche ConLeche.Cached in
theorem recordJob_eq (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat) :
    recordJob mode pins maxNatSize = recordJobR mode pins maxNatSize := by
  funext I k pd
  unfold recordJob recordJobR ConPastel.Translator.runRef
  split
  · cases checkDeclStepC mode pins (I.view k) pd { maxNatSize := maxNatSize } <;> rfl
  · rfl

end ConPastel.Leche

cake_replace ConLeche.Cached.recordJob ConPastel.Leche.recordJobR ConPastel.Leche.recordJob_eq

namespace ConPastel.Leche
-- the datatypes only the jobs use, registered before the module is tagged
cake_datatype (ConLeche.Cached.StreamIndex)
cake_datatype (ConPastel.Par.Phase1)
cake_datatype (Except (ConLeche.CheckError × Nat) (Array ConLeche.Declaration))
cake_module "Jobs"
cake_unit ConPastel.Par.phase1 ConPastel.Par.phase1Ok ConPastel.Par.jobCode ConPastel.Par.verdictCode ConPastel.Par.seqEntry
end ConPastel.Leche
