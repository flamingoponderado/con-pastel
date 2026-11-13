import ConPastel.Spec
open Lean Meta
set_option pp.explicit false
set_option pp.proofs false
#eval show MetaM Unit from do
  for n in [``ConLeche.levelsHash, ``ConLeche.Frontend.hex4, ``ConLeche.Name.decEq, ``ConLeche.Cached.checkDecls] do
    let some eq ← getUnfoldEqnFor? n (nonRec := true) | IO.println s!"{n}: no eqn"
    let ty ← inferType (mkConst eq ((← getConstInfo n).levelParams.map mkLevelParam))
    IO.println s!"=== {n}\n{← ppExpr ty}"
