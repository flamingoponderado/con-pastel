import ConPastel.Spec
open Lean Meta
#eval show MetaM Unit from do
  for n in [``String.hash, ``mixHash, ``String.Internal.append, ``ConLeche.Expr.hasStrLitGo, ``System.Platform.getNumBits] do
    let some ci := (← getEnv).find? n | IO.println s!"{n} missing"
    IO.println s!"{n} : {← ppExpr ci.type}"
    match ci with
    | .opaqueInfo o => IO.println s!"  opaque value: {← ppExpr o.value}, unsafe? {o.isUnsafe}"
    | _ => pure ()
