import ConPastel.Spec
open Lean Meta
set_option pp.proofs false
#eval show MetaM Unit from do
  let n := `ConLeche.Frontend.naiveLineLoop._sparseCasesOn_1
  let ci ← getConstInfo n
  IO.println s!"{← ppExpr ci.type}"
  IO.println s!"{(← ppExpr ci.value!).pretty.take 1200}"
  IO.println s!"isMatcher {← isMatcher n} reducibility {repr (← getReducibilityStatus n)}"
