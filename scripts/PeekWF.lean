import ConPastel.Spec
open Lean Meta
set_option pp.proofs false
#eval show MetaM Unit from do
  let n := ``ConLeche.Frontend.feedChunk
  let env ← getEnv
  let some info := Lean.Elab.WF.eqnInfoExt.find? env n | IO.println "no WF info"
  IO.println s!"declNames {info.declNames} nonRec {info.declNameNonRec} fixedPrefix?"
  let ci ← getConstInfo info.declNameNonRec
  IO.println s!"{← ppExpr ci.type}"
  let v := ci.value!
  IO.println s!"{(← ppExpr v).pretty.take 1500}"
  let ci2 ← getConstInfo n
  IO.println s!"{n} : {← ppExpr ci2.type}"
  IO.println s!"{(← ppExpr ci2.value!).pretty.take 600}"
