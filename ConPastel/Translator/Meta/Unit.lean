import ConPastel.Translator.Meta.RecCommand

/-!
# `cake_unit`: translate one Lean constant as an entry of the program's
single recursive function group

Every unit is an entry `(nᵤ, p, bodyᵤ)` of one `Dletrec` group `funs`, so its
value is `recclosure envC funs nᵤ`. Its certificate is parametric in `envC`
and `funs`:

```
∀ envC funs, (funs names distinct) → findRecFun nᵤ funs = some (p, bodyᵤ) →
  HasBoolCons envC.c → HasListCons envC.c → T.cakeHasCons envC.c → … →
  nsLookup (buildRecEnv funs envC envC.v) (.short nᵤ) = some (recclosure envC funs nᵤ) →
  (for each dependency d)
    nsLookup (buildRecEnv funs envC envC.v) (.short n_d) = some (recclosure envC funs n_d) →
    INV d (recclosure envC funs n_d) →
  INV u (recclosure envC funs nᵤ)
```

Function units are refined against the function (or, for several arguments
of a recursive function, its tupled form `c.cake_tupled`); constants are
thunks, refined against `fun _ : Unit => c`.
-/

namespace ConPastel.Translator.Meta
open Lean Meta Elab Command
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- The Lean term a unit refines, and its invariant. -/
def unitTarget (u : UnitInfo) : MetaM (Expr × Expr) := do
  let c := mkConst u.const
  match u.kind with
  | .function _ _ true =>
    let t := mkConst (u.const ++ `cake_tupled)
    return (t, ← invOf (← inferType t))
  | .function _ _ false => return (c, ← invOf (← inferType c))
  | .thunk _ _ =>
    let ty ← inferType c
    let t ← withLocalDeclD `u (mkConst ``Unit) fun x => mkLambdaFVars #[x] c
    return (t, ← mkAppM ``Arrow #[mkConst ``UNIT, ← invOf ty])

/-- Registered units mentioned in `e`. -/
def unitDeps (self : Name) (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let cs := e.getUsedConstants.filter fun c => c != self && (getUnit? env c).isSome
  return cs.toList.eraseDups.toArray

def datatypeNames : MetaM (Array Name) := do
  return ((datatypeExt.getState (← getEnv)).toList.map (·.1)).toArray

def addUnit (u : UnitInfo) : MetaM Unit :=
  modifyEnv fun env => unitExt.addEntry env u

def funTy : MetaM Expr := do mkAppM ``Prod #[mkConst ``VarN, ← mkAppM ``Prod #[mkConst ``VarN, mkConst ``Exp]]

/-- `nsLookup (buildRecEnv funs envC envC.v) (.short n) = some (recclosure envC funs n)` -/
def groupLookupTy (envC funs : Expr) (n : String) : MetaM Expr := do
  let ns ← mkAppM ``buildRecEnv #[funs, envC, ← mkAppM ``SemEnv.v #[envC]]
  mkEq (← mkAppM ``nsLookup #[ns, shortIdent n])
    (← mkAppM ``Option.some #[← mkAppM ``Value.recclosure #[envC, funs, mlString n]])

/-- Introduce the hypotheses of a unit certificate (see the module doc) and
run `k` with them. `body` is the unit's (metavariable) body. -/
def withGroupHyps {α : Type} [Inhabited α] (self : String) (param : String) (body : Expr)
    (deps : Array Name)
    (k : Expr → Expr → Expr → Expr → Array Expr → GCtx → MetaM α) : MetaM α := do
  withLocalDeclD `envC (mkApp (mkConst ``SemEnv) (mkConst ``Value)) fun envC => do
  let fty ← funTy
  withLocalDeclD `funs (← mkAppM ``List #[fty]) fun funs => do
  let nodupTy ← mkAppM ``List.Nodup #[← mkAppM ``List.map #[← withLocalDeclD `p fty fun p => do
    mkLambdaFVars #[p] (← mkAppM ``Prod.fst #[p]), funs]]
  withLocalDeclD `hnodup nodupTy fun hnodup => do
  let findTy ← mkEq (← mkAppM ``findRecFun #[mlString self, funs])
    (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[mlString param, body]])
  withLocalDeclD `hfind findTy fun hfind => do
  let envCc ← mkAppM ``SemEnv.c #[envC]
  withLocalDeclD `hbool (← mkAppM ``HasBoolCons #[envCc]) fun hbool => do
  withLocalDeclD `hlist (← mkAppM ``HasListCons #[envCc]) fun hlist => do
  let dts := (datatypeExt.getState (← getEnv)).toList.map (·.1)
  withLocalDeclsDND (dts.toArray.map fun T => (`hc, mkApp (mkConst (T ++ `cakeHasCons)) envCc)) fun hcs => do
  let hasCons : NameMap Expr := (dts.zip hcs.toList).foldl (fun m (T, h) => m.insert T h) {}
  withLocalDeclD `hself (← groupLookupTy envC funs self) fun hself => do
  let rec go : List Name → Array Expr → NameMap GlobalVar → MetaM α
    | [], acc, globals =>
      k envC funs hnodup hfind (#[envC, funs, hnodup, hfind, hbool, hlist] ++ hcs ++ #[hself] ++ acc)
        { hbool, hlist, hasCons, globals, unfoldRec := false }
    | d :: ds, acc, globals => do
      let some u := getUnit? (← getEnv) d | throwError "unit {d} missing"
      let (tgt, inv) ← unitTarget u
      let value ← mkAppM ``Value.recclosure #[envC, funs, mlString u.cname]
      withLocalDeclD `hl (← groupLookupTy envC funs u.cname) fun hl => do
      withLocalDeclD `hv (mkApp2 inv tgt value) fun hv => do
        go ds (acc ++ #[hl, hv]) (globals.insert d { cname := u.cname, value, inv, cert := hv })
  go deps.toList #[] {}

/-- Finish a unit: name the body, state and check the certificate, register. -/
def finishUnit (c : Name) (cname param : String) (kind : UnitKind) (deps : Array Name)
    (body : Expr) (hyps : Array Expr) (envC funs : Expr) (pf : Expr) (target inv : Expr) : MetaM Unit := do
  let _ := param
  let bodyI ← instantiateMVars body
  let bodyName := c ++ `cake_body
  addDecl (Declaration.defnDecl (mkDefinitionValEx bodyName [] (mkConst ``Exp) bodyI .abbrev .safe []))
  let cl ← mkAppM ``Value.recclosure #[envC, funs, mlString cname]
  let stmt ← instantiateMVars (← mkForallFVars hyps (mkApp2 inv target cl))
  -- refer to the body by its name in the statement
  let stmt := stmt.replace fun e => if e == bodyI then some (mkConst bodyName) else none
  let pf ← instantiateMVars (← mkLambdaFVars hyps pf)
  unless ← isDefEq (← inferType pf) stmt do throwError "certificate type mismatch for {c}"
  addDecl (Declaration.thmDecl (mkTheoremValEx (c ++ `cake_cert) [] stmt pf []))
  addUnit (UnitInfo.mk c cname kind (c ++ `cake_cert) (← datatypeNames) deps)

/-- The body environment of a group entry. -/
def bodyEnv (envC funs : Expr) (param : String) (xv : Expr) : MetaM Expr :=
  mkAppM ``recBodyEnv #[envC, funs, mlString param, xv]

/-- A non-recursive function unit: `c = fun x => e`. -/
def translateFunction (c : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let some val := ci.value? | throwError "{c} has no definition"
  let val ← etaExpand val
  let .lam xn xty _ _ := val | throwError "{c} is not a function"
  let deps ← unitDeps c val
  let cname := s!"%{unitCount (← getEnv)}"
  let param := "p"
  let target := mkConst c
  let inv ← invOf ci.type
  let (``Arrow, #[_, _, invA, invB]) := inv.getAppFnArgs | throwError "unexpected invariant for {c}"
  let body ← mkFreshExprMVar (mkConst ``Exp)
  withGroupHyps cname param body deps fun envC funs hnodup hfind hyps gctx => do
    let pf ← withLocalDeclD xn xty fun x => do
      withLocalDeclD `xv (mkConst ``Value) fun xv => do
      withLocalDeclD `hx (mkApp2 invA x xv) fun hx => do
        let env ← bodyEnv envC funs param xv
        let g ← mkFreshExprMVar (← mkAppM ``Eval #[env, body, mkApp invB (val.beta #[x])])
        let gst : GSt := { locals := #[{ fvar := x, cname := param, value := xv, rel := hx }] }
        let _ ← (solve g.mvarId!).run gst |>.run gctx
        let app ← mkAppOptM ``AppReturns_recclosure #[envC, funs, mlString cname, mlString param, body, xv,
          mkApp invB (mkApp target x), hnodup, hfind, g]
        mkLambdaFVars #[x, xv, hx] app
    finishUnit c cname param (.function param (c ++ `cake_body) false) deps body hyps envC funs pf target inv

/-- A constant unit, as a thunk. -/
def translateThunk (c : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let some val := ci.value? | throwError "{c} has no definition"
  let deps ← unitDeps c val
  let cname := s!"%{unitCount (← getEnv)}"
  let param := "p"
  let invT ← invOf ci.type
  let target ← withLocalDeclD `u (mkConst ``Unit) fun x => mkLambdaFVars #[x] (mkConst c)
  let inv ← mkAppM ``Arrow #[mkConst ``UNIT, invT]
  let body ← mkFreshExprMVar (mkConst ``Exp)
  withGroupHyps cname param body deps fun envC funs hnodup hfind hyps gctx => do
    let pf ← withLocalDeclD `x (mkConst ``Unit) fun x => do
      withLocalDeclD `xv (mkConst ``Value) fun xv => do
      withLocalDeclD `hx (mkApp2 (mkConst ``UNIT) x xv) fun hx => do
        let env ← bodyEnv envC funs param xv
        let g ← mkFreshExprMVar (← mkAppM ``Eval #[env, body, mkApp invT val])
        let _ ← (solve g.mvarId!).run {} |>.run gctx
        let app ← mkAppOptM ``AppReturns_recclosure #[envC, funs, mlString cname, mlString param, body, xv,
          mkApp invT (mkConst c), hnodup, hfind, g]
        mkLambdaFVars #[x, xv, hx] app
    finishUnit c cname param (.thunk param (c ++ `cake_body)) deps body hyps envC funs pf target inv

/-- A recursive function unit, by well-founded induction on the structural
argument (several arguments: tupled). -/
def translateRecursive (c : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let some eqn ← getUnfoldEqnFor? c (nonRec := true) | throwError "no unfold equation for {c}"
  let eqnTy ← inferType (mkConst eqn (ci.levelParams.map mkLevelParam))
  let deps ← unitDeps c eqnTy
  let cname := s!"%{unitCount (← getEnv)}"
  let param := "p"
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
  let body ← mkFreshExprMVar (mkConst ``Exp)
  let inv ← mkAppM ``Arrow #[invT, invB]
  withGroupHyps cname param body deps fun envC funs hnodup hfind hyps gctx₀ => do
    let cl ← mkAppM ``Value.recclosure #[envC, funs, mlString cname]
    let msr ← withLocalDeclD `p τ fun p => do
      let comp := (← tupleProjs p n)[recArg]!
      mkLambdaFVars #[p] (← mkAppM ``SizeOf.sizeOf #[comp])
    let wfr ← mkAppOptM ``measure #[τ, msr]
    let r ← mkAppOptM ``WellFoundedRelation.rel #[τ, wfr]
    let hwf ← mkAppOptM ``WellFoundedRelation.wf #[τ, wfr]
    let pfH ← withLocalDeclD `p τ fun p => do
      let ihTy ← withLocalDeclD `y τ fun y => do
        mkForallFVars #[y] (← mkArrow (mkApp2 r y p) (← withLocalDeclD `yv (mkConst ``Value) fun yv => do
          mkForallFVars #[yv] (← mkArrow (mkApp2 invT y yv) (← mkAppM ``AppReturns #[cl, yv, mkApp invB (mkApp ft y)]))))
      withLocalDeclD `ih ihTy fun ih => do
      withLocalDeclD `pv (mkConst ``Value) fun pv => do
      withLocalDeclD `hp (mkApp2 invT p pv) fun hp => do
        let env ← bodyEnv envC funs param pv
        let g ← mkFreshExprMVar (← mkAppM ``Eval #[env, body, mkApp invB (mkApp ft p)])
        let gctx := { gctx₀ with rec? := some { head := c, static := #[], ih, cl, cname, arity := n } }
        let gst : GSt := { locals := #[{ fvar := p, cname := param, value := pv, rel := hp }] }
        let _ ← (destructAndSolve g.mvarId! env invB f eqn #[] p n).run gst |>.run gctx
        let app ← mkAppOptM ``AppReturns_recclosure #[envC, funs, mlString cname, mlString param, body, pv,
          mkApp invB (mkApp ft p), hnodup, hfind, g]
        mkLambdaFVars #[p, ih, pv, hp] app
    let pf ← mkAppOptM ``arrow_of_wf #[τ, resTy, invT, invB, r, hwf, ft, cl, pfH]
    finishUnit c cname param (.function param (c ++ `cake_body) tupled) deps body hyps envC funs pf ft inv

/-- Is `c` defined by recursion (structural or well-founded)? -/
def isRecursiveDef (c : Name) : MetaM Bool := do
  let env ← getEnv
  return (Lean.Elab.Structural.eqnInfoExt.find? env c).isSome || (Lean.Elab.WF.eqnInfoExt.find? env c).isSome

def translateUnit (c : Name) : MetaM Unit := do
  if (getUnit? (← getEnv) c).isSome then return
  let ci ← getConstInfo c
  let isFn : Bool ← forallTelescope ci.type fun xs _ => pure (decide (xs.size > 0))
  if ← isRecursiveDef c then translateRecursive c
  else if isFn then translateFunction c
  else translateThunk c

elab "cake_unit " ids:ident+ : command => do
  for id in ids do
    let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    liftTermElabM <| translateUnit c

end ConPastel.Translator.Meta
