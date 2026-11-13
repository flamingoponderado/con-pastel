import ConPastel.Translator.Meta.Unit

/-!
# Primitive units

`cake_primitive key body by tac` registers a hand-written CakeML body for the
unit `key`, with a hand-proved certificate of the same shape as generated
ones (no dependencies):

```
∀ envC funs, (funs names distinct) → findRecFun n funs = some ("p", body) →
  HasBoolCons envC.c → HasListCons envC.c →
  nsLookup (buildRecEnv funs envC envC.v) (.short n) = some (recclosure envC funs n) →
  INV key (recclosure envC funs n)
```

Primitives are registered before any datatype, so they take no
`cakeHasCons` hypotheses.
-/

namespace ConPastel.Translator.Meta
open Lean Meta Elab Command Term
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

def primitiveStatement (key body : Expr) (cname : String) : MetaM Expr := do
  let inv ← invOf (← inferType key)
  let param := "p"
  withLocalDeclD `envC (mkApp (mkConst ``SemEnv) (mkConst ``Value)) fun envC => do
  let fty ← funTy
  withLocalDeclD `funs (← mkAppM ``List #[fty]) fun funs => do
  let nodupTy ← mkAppM ``List.Nodup #[← mkAppM ``List.map #[← withLocalDeclD `p fty fun p => do
    mkLambdaFVars #[p] (← mkAppM ``Prod.fst #[p]), funs]]
  withLocalDeclD `hnodup nodupTy fun hnodup => do
  let findTy ← mkEq (← mkAppM ``findRecFun #[mlString cname, funs])
    (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[mlString param, body]])
  withLocalDeclD `hfind findTy fun hfind => do
  let envCc ← mkAppM ``SemEnv.c #[envC]
  withLocalDeclD `hbool (← mkAppM ``HasBoolCons #[envCc]) fun hbool => do
  withLocalDeclD `hlist (← mkAppM ``HasListCons #[envCc]) fun hlist => do
  withLocalDeclD `hself (← groupLookupTy envC funs cname) fun hself => do
    let cl ← mkAppM ``Value.recclosure #[envC, funs, mlString cname]
    mkForallFVars #[envC, funs, hnodup, hfind, hbool, hlist, hself] (mkApp2 inv key cl)

elab "cake_primitive " k:term:max b:term:max " by " tac:tacticSeq : command => do
  liftTermElabM do
    let key ← instantiateMVars (← elabTerm k none)
    synthesizeSyntheticMVarsNoPostponing
    let key ← instantiateMVars key
    if (getUnit? (← getEnv) key).isSome then throwError "{key} already has a unit"
    unless (datatypeExt.getState (← getEnv)).isEmpty do
      throwError "primitives must be registered before any datatype"
    let body ← instantiateMVars (← elabTerm b (mkConst ``Exp))
    synthesizeSyntheticMVarsNoPostponing
    let (uname, cname) ← freshUnit
    addDecl (Declaration.defnDecl (mkDefinitionValEx (uname ++ `body) [] (mkConst ``Exp) (← instantiateMVars body)
      .abbrev .safe []))
    let stmt ← primitiveStatement key (mkConst (uname ++ `body)) cname
    let mvar ← mkFreshExprMVar stmt
    let remaining ← Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
    unless remaining.isEmpty do throwError "primitive certificate for {key} not proved"
    let pf ← instantiateMVars mvar
    addDecl (Declaration.thmDecl (mkTheoremValEx (uname ++ `cert) [] stmt pf []))
    let isFn : Bool ← forallTelescope (← inferType key) fun xs _ => pure (decide (xs.size > 0))
    let kind := if isFn then UnitKind.function "p" (uname ++ `body) false else .thunk "p" (uname ++ `body)
    addUnit { key, name := uname, cname, kind, cert := uname ++ `cert, datatypes := #[], deps := #[] }

end ConPastel.Translator.Meta
