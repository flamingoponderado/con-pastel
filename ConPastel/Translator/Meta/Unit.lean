import ConPastel.Translator.Meta.RecCommand

/-!
# `cake_unit`: translate one Lean constant as a program unit

A unit's certificate is parametric in the environment and in the values of
the units it calls:

```
∀ env, HasBoolCons env.c → T.cakeHasCons env.c → … →
  ∀ v₁, INV h₁ v₁ → nsLookup env.v (.short n₁) = some v₁ → … →
  Eval env e (INV c)                                   -- plain units
  Arrow A B c (recclosure env [(n, p, body)] n)         -- recursive units
```

so certificates compose without knowing how the environment is built.
-/

namespace ConPastel.Translator.Meta
open Lean Meta Elab Command
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- The Lean constant a unit is called through, and its CakeML name. -/
def unitTarget (u : UnitInfo) : Name × String :=
  match u.kind with
  | .recursive _ _ true => (u.const ++ `cake_tupled, (u.const ++ `cake_tupled).toString)
  | _ => (u.const, u.cname)

/-- Registered units mentioned in `e`. -/
def unitDeps (self : Name) (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let cs := e.getUsedConstants.filter fun c => c != self && (getUnit? env c).isSome
  return cs.toList.eraseDups.toArray

/-- Introduce the shared hypotheses of a unit certificate and run `k` with
the translation context. -/
def withUnitHyps {α : Type} [Inhabited α] (deps : Array Name)
    (k : Expr → Array Expr → GCtx → MetaM α) : MetaM α := do
  withLocalDeclD `env (mkApp (mkConst ``SemEnv) (mkConst ``Value)) fun env => do
  withLocalDeclD `hbool (← mkAppM ``HasBoolCons #[← mkAppM ``SemEnv.c #[env]]) fun hbool => do
  withLocalDeclD `hlist (← mkAppM ``HasListCons #[← mkAppM ``SemEnv.c #[env]]) fun hlist => do
  let dts := (datatypeExt.getState (← getEnv)).toList.map (·.1)
  let envc ← mkAppM ``SemEnv.c #[env]
  withLocalDeclsDND (dts.toArray.map fun T => (`hc, mkApp (mkConst (T ++ `cakeHasCons)) envc)) fun hcs => do
  let hasCons : NameMap Expr := (dts.zip hcs.toList).foldl (fun m (T, h) => m.insert T h) {}
  let rec go : List Name → Array Expr → NameMap GlobalVar → MetaM α
    | [], acc, globals => k env (#[env, hbool, hlist] ++ hcs ++ acc) { hbool, hlist, hasCons, globals }
    | d :: ds, acc, globals => do
      let some u := getUnit? (← getEnv) d | throwError "unit {d} missing"
      let (tgt, cname) := unitTarget u
      let inv ← invOf (← inferType (mkConst tgt))
      withLocalDeclD `w (mkConst ``Value) fun w => do
      withLocalDeclD `hw (mkApp2 inv (mkConst tgt) w) fun hw => do
      withLocalDeclD `hl (← mkEq (← mkAppM ``nsLookup #[← mkAppM ``SemEnv.v #[env], shortIdent cname])
          (← mkAppM ``Option.some #[w])) fun hl => do
        go ds (acc ++ #[w, hw, hl]) (globals.insert tgt { cname, value := w, inv, cert := hw })
  go deps.toList #[] {}

def addUnit (u : UnitInfo) : MetaM Unit :=
  modifyEnv fun env => unitExt.addEntry env u

def datatypeNames : MetaM (Array Name) := do
  return ((datatypeExt.getState (← getEnv)).toList.map (·.1)).toArray

/-- A plain (non-recursive) unit: `Dlet (pvar c) exp`. -/
def translatePlain (c : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let some val := ci.value? | throwError "{c} has no definition"
  let deps ← unitDeps c val
  let inv ← invOf ci.type
  withUnitHyps deps fun env hyps gctx => do
    let ce ← mkFreshExprMVar (mkConst ``Exp)
    let g ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv val])
    let _ ← (solve g.mvarId!).run {} |>.run gctx
    let ceI ← instantiateMVars ce
    let expName := c ++ `cake_exp
    addDecl (Declaration.defnDecl (mkDefinitionValEx expName [] (mkConst ``Exp) ceI .abbrev .safe []))
    let stmt ← mkForallFVars hyps (← mkAppM ``Eval #[env, mkConst expName, mkApp inv (mkConst c)])
    let pf ← mkLambdaFVars hyps (← instantiateMVars g)
    unless ← isDefEq (← inferType pf) stmt do throwError "certificate type mismatch for {c}"
    addDecl (Declaration.thmDecl (mkTheoremValEx (c ++ `cake_cert) [] stmt pf []))
  let dts ← datatypeNames
  let expN := c ++ `cake_exp
  let certN := c ++ `cake_cert
  let u : UnitInfo := UnitInfo.mk c c.toString (UnitKind.plain expN) certN dts deps
  addUnit u

/-- A recursive unit: `Dletrec [(name, param, body)]`. With more than one
argument the closure takes a nested tuple (`c.cake_tupled`). -/
def translateRecursive (c : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let some eqn ← getUnfoldEqnFor? c (nonRec := true) | throwError "no unfold equation for {c}"
  let eqnTy ← inferType (mkConst eqn (ci.levelParams.map mkLevelParam))
  let deps ← unitDeps c eqnTy
  forallTelescope ci.type fun xs resTy => do
  let n := xs.size
  let tys ← xs.mapM inferType
  let tupled := n > 1
  let τ ← tupleTy tys.toList
  let invT ← invOf τ
  let invB ← invOf resTy
  let f := mkConst c
  let ft ← if tupled then do
      let tupName := c ++ `cake_tupled
      let tupVal ← withLocalDeclD `p τ fun p => do mkLambdaFVars #[p] (mkAppN f (← tupleProjs p n).toArray)
      addDecl (Declaration.defnDecl (mkDefinitionValEx tupName [] (← mkArrow τ resTy) tupVal .abbrev .safe []))
      pure (mkConst tupName)
    else pure f
  let recArg ← if tupled then do
      let some k ← structRecArg? c | throwError "{c}: only structural recursion is supported for now"
      pure k
    else pure 0
  let fname := if tupled then (c ++ `cake_tupled).toString else c.toString
  let pname := "p"
  withUnitHyps deps fun envC hyps gctx₀ => do
    let body ← mkFreshExprMVar (mkConst ``Exp)
    let funTy ← mkAppM ``Prod #[mkConst ``VarN, ← mkAppM ``Prod #[mkConst ``VarN, mkConst ``Exp]]
    let funs ← mkListLit funTy [← mkAppM ``Prod.mk #[mlString fname, ← mkAppM ``Prod.mk #[mlString pname, body]]]
    let cl ← mkAppM ``Value.recclosure #[envC, funs, mlString fname]
    let msr ← withLocalDeclD `p τ fun p => do
      let comp := (← tupleProjs p n)[recArg]!
      mkLambdaFVars #[p] (← mkAppM ``SizeOf.sizeOf #[comp])
    let wfr ← mkAppOptM ``measure #[τ, msr]
    let r ← mkAppOptM ``WellFoundedRelation.rel #[τ, wfr]
    let hwf ← mkAppOptM ``WellFoundedRelation.wf #[τ, wfr]
    let nodupTy ← mkAppM ``List.Nodup #[← mkAppM ``List.map #[← withLocalDeclD `p funTy fun p => do
      mkLambdaFVars #[p] (← mkAppM ``Prod.fst #[p]), funs]]
    let hnodup ← mkFreshExprMVar nodupTy
    let findTy ← mkEq (← mkAppM ``findRecFun #[mlString fname, funs])
      (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[mlString pname, body]])
    let hfind ← mkFreshExprMVar findTy
    let pfH ← withLocalDeclD `p τ fun p => do
      let ihTy ← withLocalDeclD `y τ fun y => do
        mkForallFVars #[y] (← mkArrow (mkApp2 r y p) (← withLocalDeclD `yv (mkConst ``Value) fun yv => do
          mkForallFVars #[yv] (← mkArrow (mkApp2 invT y yv) (← mkAppM ``AppReturns #[cl, yv, mkApp invB (mkApp ft y)]))))
      withLocalDeclD `ih ihTy fun ih => do
      withLocalDeclD `pv (mkConst ``Value) fun pv => do
      withLocalDeclD `hp (mkApp2 invT p pv) fun hp => do
        let env ← mkAppM ``recBodyEnv #[envC, funs, mlString pname, pv]
        let g ← mkFreshExprMVar (← mkAppM ``Eval #[env, body, mkApp invB (mkApp ft p)])
        let gctx := { gctx₀ with rec? := some { head := c, static := #[], ih, cl, cname := fname, arity := n } }
        let gst : GSt := { locals := #[{ fvar := p, cname := pname, value := pv, rel := hp }] }
        let _ ← (destructAndSolve g.mvarId! env invB f eqn #[] p n).run gst |>.run gctx
        let app ← mkAppOptM ``AppReturns_recclosure #[envC, funs, mlString fname, mlString pname, body, pv,
          mkApp invB (mkApp ft p), hnodup, hfind, g]
        mkLambdaFVars #[p, ih, pv, hp] app
    hnodup.mvarId!.assign (← closeWith (← instantiateMVars nodupTy) (← `(tactic| decide)))
    hfind.mvarId!.assign (← closeWith (← instantiateMVars findTy) (← `(tactic| simp [findRecFun])))
    let pf ← instantiateMVars (← mkAppOptM ``arrow_of_wf #[τ, resTy, invT, invB, r, hwf, ft, cl, pfH])
    let bodyI ← instantiateMVars body
    let bodyName := c ++ `cake_body
    addDecl (Declaration.defnDecl (mkDefinitionValEx bodyName [] (mkConst ``Exp) bodyI .abbrev .safe []))
    let funsN ← mkListLit funTy [← mkAppM ``Prod.mk #[mlString fname, ← mkAppM ``Prod.mk #[mlString pname, mkConst bodyName]]]
    let clN ← mkAppM ``Value.recclosure #[envC, funsN, mlString fname]
    let stmt ← mkForallFVars hyps (mkApp2 (← mkAppM ``Arrow #[invT, invB]) ft clN)
    let pf ← mkLambdaFVars hyps pf
    unless ← isDefEq (← inferType pf) stmt do throwError "certificate type mismatch for {c}"
    addDecl (Declaration.thmDecl (mkTheoremValEx (c ++ `cake_cert) [] stmt pf []))
  let dts ← datatypeNames
  let u : UnitInfo := UnitInfo.mk c fname (UnitKind.recursive pname (c ++ `cake_body) tupled) (c ++ `cake_cert) dts deps
  addUnit u

/-- Is `c` defined by recursion (structural or well-founded)? -/
def isRecursiveDef (c : Name) : MetaM Bool := do
  let env ← getEnv
  return (Lean.Elab.Structural.eqnInfoExt.find? env c).isSome || (Lean.Elab.WF.eqnInfoExt.find? env c).isSome

def translateUnit (c : Name) : MetaM Unit := do
  if (getUnit? (← getEnv) c).isSome then return
  if ← isRecursiveDef c then translateRecursive c else translatePlain c

elab "cake_unit " ids:ident+ : command => do
  for id in ids do
    let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    liftTermElabM <| translateUnit c

end ConPastel.Translator.Meta
