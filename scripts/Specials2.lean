import ConPastel.Spec
open Lean Meta
#eval show MetaM Unit from do
  for n in [``String.append, ``instAppendString, ``String.push, ``USize.size, ``System.Platform.numBits, ``String.decEq] do
    let some ci := (← getEnv).find? n | IO.println s!"{n} missing"
    match ci with
    | .defnInfo d => IO.println s!"{n} := {← ppExpr d.value}"
    | .opaqueInfo d => IO.println s!"{n} OPAQUE"
    | _ => IO.println s!"{n} other {ci.isTheorem}"
