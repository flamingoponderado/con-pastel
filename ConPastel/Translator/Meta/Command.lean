import ConPastel.Translator.Meta.Core

/-! # `cake_translate`: translate a closed definition -/

namespace ConPastel.Translator.Meta
open Lean Meta Elab Command
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

def translateClosed (c : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let some body := ci.value? | throwError "{c} has no definition"
  let inv ← invOf ci.type
  withLocalDeclD `env (mkConst ``SemEnv [] |>.app (mkConst ``Value)) fun env => do
  withLocalDeclD `hbool (← mkAppM ``HasBoolCons #[← mkAppM ``SemEnv.c #[env]]) fun hbool => do
    let ctx : Ctx := { env, hbool }
    let (ce, pf) ← (transExpr body).run ctx
    let ce ← instantiateMVars ce
    let expName := c ++ `cake
    let expTy := mkConst ``Exp
    addDecl (Declaration.defnDecl (mkDefinitionValEx expName [] expTy ce .abbrev .safe []))
    let stmt ← mkForallFVars #[env, hbool]
      (← mkAppM ``Eval #[env, mkConst expName, mkApp inv (mkConst c)])
    let pf ← mkLambdaFVars #[env, hbool] pf
    let pf ← instantiateMVars pf
    unless ← isDefEq (← inferType pf) stmt do
      throwError "certificate type mismatch:\n{← inferType pf}\nvs\n{stmt}"
    addDecl (Declaration.thmDecl (mkTheoremValEx (c ++ `cake_eval) [] stmt pf []))

elab "cake_translate " id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM <| translateClosed c

end ConPastel.Translator.Meta
