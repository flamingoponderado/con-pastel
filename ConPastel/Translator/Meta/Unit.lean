import ConPastel.Translator.Meta.RecCommand
import ConPastel.Translator.Meta.Keys

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
  match u.kind with
  | .function _ _ true =>
    let t := mkConst (u.name ++ `tupled)
    return (t, ← invOf (← inferType t))
  | .function _ _ false => return (u.key, ← invOf (← inferType u.key))
  | .thunk _ _ =>
    let ty ← inferType u.key
    let t ← withLocalDeclD `u (mkConst ``Unit) fun x => mkLambdaFVars #[x] u.key
    return (t, ← mkAppM ``Arrow #[mkConst ``UNIT, ← invOf ty])

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
    (deps : Array Expr)
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
  let reps := assumeReplaceExt.getState (← getEnv)
  withLocalDeclsDND (reps.map fun (_, _, P) => (`ha, P)) fun has => do
  let assumed := (reps.zip has).map fun ((k, r, _), h) => (k, r, h)
  let rec go : List Expr → Array Expr → Std.HashMap Expr GlobalVar → MetaM α
    | [], acc, globals =>
      k envC funs hnodup hfind (#[envC, funs, hnodup, hfind, hbool, hlist] ++ hcs ++ #[hself] ++ has ++ acc)
        { hbool, hlist, hasCons, globals, unfoldRec := false, assumed }
    | d :: ds, acc, globals => do
      let some u := getUnit? (← getEnv) d | throwError "unit {d} missing"
      let (tgt, inv) ← unitTarget u
      let value ← mkAppM ``Value.recclosure #[envC, funs, mlString u.cname]
      withLocalDeclD `hl (← groupLookupTy envC funs u.cname) fun hl => do
      withLocalDeclD `hv (mkApp2 inv tgt value) fun hv => do
        go ds (acc ++ #[hl, hv]) (globals.insert d { cname := u.cname, value, inv, cert := hv })
  go deps.toList #[] {}

/-- Finish a unit: name the body, state and check the certificate, register. -/
def finishUnit (key : Expr) (uname : Name) (cname : String) (kind : UnitKind) (deps : Array Expr)
    (body : Expr) (hyps : Array Expr) (envC funs : Expr) (pf : Expr) (target inv : Expr) : MetaM Unit := do
  let bodyI ← instantiateMVars body
  let bodyName := uname ++ `body
  addDecl (Declaration.defnDecl (mkDefinitionValEx bodyName [] (mkConst ``Exp) bodyI .abbrev .safe []))
  let cl ← mkAppM ``Value.recclosure #[envC, funs, mlString cname]
  let stmt ← instantiateMVars (← mkForallFVars hyps (mkApp2 inv target cl))
  let stmt := stmt.replace fun e => if e == bodyI then some (mkConst bodyName) else none
  let pf ← instantiateMVars (← mkLambdaFVars hyps pf)
  unless ← isDefEq (← inferType pf) stmt do throwError "certificate type mismatch for {key}"
  if pf.hasFVar || stmt.hasFVar || pf.hasMVar then
    let fvs := (collectFVars {} pf).fvarIds ++ (collectFVars {} stmt).fvarIds
    let descr ← fvs.toList.mapM fun fv => do
      match (← getLCtx).find? fv with
      | some d => pure m!"{d.userName} : {d.type}"
      | none => pure m!"{mkFVar fv} (not in context)"
    throwError "certificate for {key} has leaked locals (mvars: {pf.hasMVar}): {descr}"
  addDecl (Declaration.thmDecl (mkTheoremValEx (uname ++ `cert) [] stmt pf []))
  let assumes := (assumeReplaceExt.getState (← getEnv)).map (·.2.2)
  let depNames ← deps.mapM fun d => do
    let some du := getUnit? (← getEnv) d | throwError "dependency {d} of {key} is not a unit"
    pure du.name
  let datatypes ← datatypeNames
  addUnit { key, name := uname, cname, kind, cert := uname ++ `cert, datatypes, deps, assumes, depNames }

/-- The body environment of a group entry. -/
def bodyEnv (envC funs : Expr) (param : String) (xv : Expr) : MetaM Expr :=
  mkAppM ``recBodyEnv #[envC, funs, mlString param, xv]

/-- Fresh unit names. -/
def freshUnit : MetaM (Name × String) := do
  let env ← getEnv
  let k := unitCount env
  match cakeTagExt.getState env with
  | some t => return (Name.mkStr (unitNamespace env) s!"u{k}", s!"%{t}.{k}")
  | none => return (Name.mkStr `ConPastel.Cake s!"u{k}", s!"%{k}")

/-- The definition of a unit key `f static…`. -/
def keyValue (key : Expr) : MetaM Expr := do
  let .const c lvls := key.getAppFn | throwError "unit key {key} is not a constant application"
  let ci ← getConstInfo c
  unless ci.hasValue do throwError "{c} has no definition"
  return (mkAppN (← instantiateValueLevelParams ci lvls) key.getAppArgs).headBeta

/-- A function unit whose first data argument is followed by a proof. -/
def translateFunctionP (key val : Expr) (xn : Name) (xty invA invB : Expr) (deps : Array Expr) : MetaM Unit := do
  let (uname, cname) ← freshUnit
  let param := "p"
  let inv ← invOf (← inferType key)
  let body ← mkFreshExprMVar (mkConst ``Exp)
  withGroupHyps cname param body deps fun envC funs hnodup hfind hyps gctx => do
    let pf ← withLocalDeclD xn xty fun x => do
      withLocalDeclD `xv (mkConst ``Value) fun xv => do
      withLocalDeclD `hx (mkApp2 invA x xv) fun hx => do
      let .forallE hn p _ _ ← whnfR (← inferType (mkApp key x)) | throwError "expected a proof argument"
      withLocalDeclD hn p fun hp => do
        let env ← bodyEnv envC funs param xv
        let bodyT := (val.beta #[x, hp])
        let g ← mkFreshExprMVar (← mkAppM ``Eval #[env, body, mkApp (invB.beta #[x, hp]) bodyT])
        let gst : GSt := { locals := #[{ fvar := x, cname := param, value := xv, rel := hx }] }
        let _ ← (solve g.mvarId!).run gst |>.run gctx
        let app ← withTransparency .all <| mkAppOptM ``AppReturns_recclosure #[envC, funs, mlString cname, mlString param, body, xv,
          mkApp (invB.beta #[x, hp]) (mkApp2 key x hp), hnodup, hfind, g]
        mkLambdaFVars #[x, xv, hx, hp] app
    finishUnit key uname cname (.function param (uname ++ `body) false) deps body hyps envC funs pf key inv

def mergeDeps (a b : Array Expr) : Array Expr :=
  b.foldl (fun acc d => if acc.contains d then acc else acc.push d) a

/-- A non-recursive function unit: `key = fun x => e`. -/
def translateFunction (key : Expr) (extra : Array Expr := #[]) : MetaM Unit := do
  let val ← etaExpand (← keyValue key)
  let .lam xn xty _ _ := val | throwError "{key} is not a function"
  let deps := mergeDeps (← unitDepsOf key val) extra
  let (uname, cname) ← freshUnit
  let param := "p"
  let inv ← invOf (← inferType key)
  -- `Arrow A B` or `DARROW A B` (B depending on the argument)
  if let (``DARROWP, #[_, _, _, invA, invB]) := inv.getAppFnArgs then
    return ← translateFunctionP key val xn xty invA invB deps
  let (invA, invBAt) ← match inv.getAppFnArgs with
    | (``Arrow, #[_, _, invA, invB]) => pure (invA, fun (_ : Expr) => invB)
    | (``DARROW, #[_, _, invA, invB]) => pure (invA, fun x => invB.beta #[x])
    | _ => throwError "unexpected invariant for {key}"
  let body ← mkFreshExprMVar (mkConst ``Exp)
  withGroupHyps cname param body deps fun envC funs hnodup hfind hyps gctx => do
    let pf ← withLocalDeclD xn xty fun x => do
      let invB := invBAt x
      withLocalDeclD `xv (mkConst ``Value) fun xv => do
      withLocalDeclD `hx (mkApp2 invA x xv) fun hx => do
        let env ← bodyEnv envC funs param xv
        let g ← mkFreshExprMVar (← mkAppM ``Eval #[env, body, mkApp invB (val.beta #[x])])
        let gst : GSt := { locals := #[{ fvar := x, cname := param, value := xv, rel := hx }] }
        let _ ← (solve g.mvarId!).run gst |>.run gctx
        let app ← withTransparency .all <| mkAppOptM ``AppReturns_recclosure #[envC, funs, mlString cname, mlString param, body, xv,
          mkApp invB (mkApp key x), hnodup, hfind, g]
        mkLambdaFVars #[x, xv, hx] app
    finishUnit key uname cname (.function param (uname ++ `body) false) deps body hyps envC funs pf key inv

/-- A constant unit, as a thunk. -/
def translateThunk (key : Expr) (extra : Array Expr := #[]) : MetaM Unit := do
  let val ← keyValue key
  let deps := mergeDeps (← unitDepsOf key val) extra
  let (uname, cname) ← freshUnit
  let param := "p"
  let invT ← invOf (← inferType key)
  let target ← withLocalDeclD `u (mkConst ``Unit) fun x => mkLambdaFVars #[x] key
  let inv ← mkAppM ``Arrow #[mkConst ``UNIT, invT]
  let body ← mkFreshExprMVar (mkConst ``Exp)
  withGroupHyps cname param body deps fun envC funs hnodup hfind hyps gctx => do
    let pf ← withLocalDeclD `x (mkConst ``Unit) fun x => do
      withLocalDeclD `xv (mkConst ``Value) fun xv => do
      withLocalDeclD `hx (mkApp2 (mkConst ``UNIT) x xv) fun hx => do
        let env ← bodyEnv envC funs param xv
        let g ← mkFreshExprMVar (← mkAppM ``Eval #[env, body, mkApp invT val])
        let _ ← (solve g.mvarId!).run {} |>.run gctx
        let app ← withTransparency .all <| mkAppOptM ``AppReturns_recclosure #[envC, funs, mlString cname, mlString param, body, xv,
          mkApp invT key, hnodup, hfind, g]
        mkLambdaFVars #[x, xv, hx] app
    finishUnit key uname cname (.thunk param (uname ++ `body)) deps body hyps envC funs pf target inv

/-- The parts of a well-founded definition's unfolding `v` (its value applied
to the arguments): `c._unary fixed packed` or (one varying argument)
`WellFounded.Nat.fix … packed`. Returns `(fixed, packed, α, motive, measure, F)`. -/
def wfParts (c : Name) (v : Expr) : MetaM (Option (Array Expr × Expr × Expr × Expr × Expr × Expr)) := do
  let some info := Lean.Elab.WF.eqnInfoExt.find? (← getEnv) c | return none
  if let .const un ulvls := v.getAppFn then
    if un == info.declNameNonRec then
      let fixed := v.getAppArgs.pop
      let u := (mkAppN (← instantiateValueLevelParams (← getConstInfo un) ulvls) fixed).headBeta
      let (``WellFounded.Nat.fix, #[α, motive, m, F]) := u.getAppFnArgs | return none
      return some (fixed, v.getAppArgs.back!, α, motive, m, F)
  if let (``WellFounded.Nat.fix, #[α, motive, m, F, x]) := v.getAppFnArgs then
    return some (#[], x, α, motive, m, F)
  return none

/-- The termination measure of a recursive unit, as a function of the tuple of
its arguments: `sizeOf` of the structural argument, or the measure of a
`termination_by` definition (`WellFounded.Nat.fix` in its `_unary` form). -/
def recursionMeasure (key : Expr) (c : Name) (static : Array Expr) (n : Nat) (τ : Expr) : MetaM Expr := do
  let env ← getEnv
  if (Lean.Elab.WF.eqnInfoExt.find? env c).isSome then
    withLocalDeclD `p τ fun p => do
      let projs ← tupleProjs p n
      let v := (mkAppN (← keyValue key) projs.toArray).headBeta
      let some (_, packed, _, _, m, _) ← wfParts c v
        | throwError "{c}: well-founded recursion of this shape is not supported yet: {v}"
      mkLambdaFVars #[p] (m.beta #[packed]).headBeta
  else
    let some k ← structRecArg? c | throwError "{c}: no recursion information"
    withLocalDeclD `p τ fun p => do
      let comp := (← tupleProjs p n)[k - static.size]!
      mkLambdaFVars #[p] (← mkAppM ``SizeOf.sizeOf #[comp])

/-- For a well-founded definition over the data parameters `xs`: for each,
whether it is unchanged by recursive calls, else its index among the packed
components; and the number of packed components. -/
def wfArgSources (key : Expr) (c : Name) (xs : Array Expr) : MetaM (Array (Bool × Nat) × Nat) := do
  let v := (mkAppN (← keyValue key) xs).headBeta
  let some (fixed, packed, _) ← wfParts c v | return (#[], 0)
  let nPacked := if fixed.isEmpty && !(v.getAppFn.isConst && !v.isAppOf ``WellFounded.Nat.fix) then 1
    else key.getAppArgs.size + xs.size - fixed.size
  let comps := psigmaComps packed nPacked
  let src ← xs.mapM fun x => do
    if let some k := comps.findIdx? (· == x) then return (false, k)
    return (true, 0)
  unless src.any (!·.1) do throwError "{c}: no varying argument found in {v}"
  return (src, nPacked)

/-- For a well-founded definition, its unfolding as its functional:
`f as = F ⟨as…⟩ (fun y h => recCall (fun y => f as[y]) y h)`, so that each
recursive call carries Lean's own decreasing proof. -/
def wfFunctionalEqn (key : Expr) (c : Name) (src : Array (Bool × Nat)) (nPacked : Nat) (as : Array Expr) :
    MetaM (Option Expr) := do
  let v := (mkAppN (← keyValue key) as).headBeta
  let some (_, packed, α, motive, m, F) ← wfParts c v | return none
  let fty ← whnf (← instantiateForall (← inferType F) #[packed])
  let .forallE _ recTy _ _ := fty | return none
  let recFn ← forallTelescope recTy fun ys _ => do
    unless ys.size == 2 do throwError "unexpected well-founded functional for {c}"
    let gf ← withLocalDeclD `y α fun y' => do
      let comps := psigmaComps y' nPacked
      let args := (as.zip src).map fun (a, (unch, k)) => if unch then a else comps[k]!
      mkLambdaFVars #[y'] (mkAppN key args)
    mkLambdaFVars ys (← mkAppOptM ``recCall #[α, motive, ← inferType ys[1]!, gf, ys[0]!, ys[1]!])
  let rhs := (mkApp2 F packed recFn).headBeta
  let pf ← mkAppOptM ``WellFounded.Nat.fix_eq #[α, motive, m, F, packed]
  return some (← mkExpectedTypeHint pf (← mkEq (mkAppN key as) rhs))

/-- A recursive function unit, by well-founded induction on the structural
argument (several arguments: tupled). -/
def translateRecursive (key : Expr) (extra : Array Expr := #[]) (functional : Bool := false) : MetaM Unit := do
  let .const c lvls := key.getAppFn | throwError "bad key"
  let static := key.getAppArgs
  let some eqn ← getUnfoldEqnFor? c (nonRec := true) | throwError "no unfold equation for {c}"
  let eqnApp (as : Array Expr) : MetaM Expr := pure (mkAppN (mkConst eqn lvls) (static ++ as))
  let deps ← forallTelescope (← inferType key) fun xs _ => do
    return mergeDeps (← unitDepsOf key (← inferType (← eqnApp xs))) extra
  let (uname, cname) ← freshUnit
  let param := "p"
  -- the parameter types, the result type and where arguments come from; the
  -- translation itself runs outside the parameters' scope (no leaks)
  let (n, tys, resAbs, resTy0, dep, wfSrc) ← forallTelescope (← inferType key) fun xs resTy => do
    let tys ← xs.mapM inferType
    if tys.any (·.hasFVar) then
      throwError "{key}: dependent parameter types are not supported yet"
    let wfSrc ← try wfArgSources key c xs catch _ => pure (#[], 0)
    return (xs.size, tys, ← mkLambdaFVars xs resTy, resTy, resTy.hasFVar, wfSrc)
  -- the result type for given arguments (dependent results, e.g. `Decidable (a = b)`)
  let resOf (as : Array Expr) : Expr := resAbs.beta as
  let tupled := n > 1
  let τ ← tupleTy tys.toList
  let invT ← invOf τ
  -- the result invariant for given arguments, and as a function of the tuple
  let invFor (as : Array Expr) : MetaM Expr := invOf (resOf as)
  let invBf ← withLocalDeclD `p τ fun p => do mkLambdaFVars #[p] (← invFor (← tupleProjs p n).toArray)
  let invBat (y : Expr) : Expr := if dep then invBf.beta #[y] else invBf.bindingBody!
  let f := key
  let ftTy ← withLocalDeclD `p τ fun p => do mkForallFVars #[p] (resOf (← tupleProjs p n).toArray)
  let ft ← if tupled then do
      let tupName := uname ++ `tupled
      let tupVal ← withLocalDeclD `p τ fun p => do mkLambdaFVars #[p] (mkAppN f (← tupleProjs p n).toArray)
      addDecl (Declaration.defnDecl (mkDefinitionValEx tupName [] ftTy tupVal .abbrev .safe []))
      pure (mkConst tupName)
    else pure f
  let msr ← recursionMeasure key c static n τ
  let body ← mkFreshExprMVar (mkConst ``Exp)
  let inv ← if dep then mkAppM ``DARROW #[invT, invBf] else mkAppM ``Arrow #[invT, invBf.bindingBody!]
  withGroupHyps cname param body deps fun envC funs hnodup hfind hyps gctx₀ => do
    let cl ← mkAppM ``Value.recclosure #[envC, funs, mlString cname]
    let wfr ← mkAppOptM ``measure #[τ, msr]
    let r ← mkAppOptM ``WellFoundedRelation.rel #[τ, wfr]
    let hwf ← mkAppOptM ``WellFoundedRelation.wf #[τ, wfr]
    let pfH ← withLocalDeclD `p τ fun p => do
      let ihTy ← withLocalDeclD `y τ fun y => do
        mkForallFVars #[y] (← mkArrow (mkApp2 r y p) (← withLocalDeclD `yv (mkConst ``Value) fun yv => do
          mkForallFVars #[yv] (← mkArrow (mkApp2 invT y yv) (← mkAppM ``AppReturns #[cl, yv, mkApp (invBat y) (mkApp ft y)]))))
      withLocalDeclD `ih ihTy fun ih => do
      withLocalDeclD `pv (mkConst ``Value) fun pv => do
      withLocalDeclD `hp (mkApp2 invT p pv) fun hp => do
        let env ← bodyEnv envC funs param pv
        let g ← mkFreshExprMVar (← mkAppM ``Eval #[env, body, mkApp (invBat p) (mkApp ft p)])
        let depInfo : Option (Expr × Expr) := if dep then some (invBf, ft) else none
        let rf : RecFn := { head := c, static, ih, cl, cname, arity := n, argSrc := wfSrc.1, nPacked := wfSrc.2, lvls, dep? := depInfo }
        let gctx := { gctx₀ with rec? := some rf }
        let gst : GSt := { locals := #[{ fvar := p, cname := param, value := pv, rel := hp }] }
        let eqnAppS (as : Array Expr) : MetaM Expr := do
          if wfSrc.1.isEmpty || !functional then eqnApp as else
          match ← wfFunctionalEqn key c wfSrc.1 wfSrc.2 as with
          | some e => pure e
          | none => eqnApp as
        let _ ← (destructAndSolve g.mvarId! env invFor f eqnAppS #[] p n).run gst |>.run gctx
        let app ← withTransparency .all <| mkAppOptM ``AppReturns_recclosure #[envC, funs, mlString cname, mlString param, body, pv,
          mkApp (invBat p) (mkApp ft p), hnodup, hfind, g]
        mkLambdaFVars #[p, ih, pv, hp] app
    let βf ← withLocalDeclD `p τ fun p => do mkLambdaFVars #[p] (resOf (← tupleProjs p n).toArray)
    let pf ← withTransparency .all <| if dep then
        mkAppOptM ``darrow_of_wf #[τ, βf, invT, invBf, r, hwf, ft, cl, pfH]
      else mkAppOptM ``arrow_of_wf #[τ, resTy0, invT, invBf.bindingBody!, r, hwf, ft, cl, pfH]
    finishUnit key uname cname (.function param (uname ++ `body) tupled) deps body hyps envC funs pf ft inv

/-- Is `c` defined by recursion (structural or well-founded)? -/
def isRecursiveDef (c : Name) : MetaM Bool := do
  let env ← getEnv
  return (Lean.Elab.Structural.eqnInfoExt.find? env c).isSome || (Lean.Elab.WF.eqnInfoExt.find? env c).isSome

def translateUnitOnce (key : Expr) (extra : Array Expr) : MetaM Unit := do
  if (getUnit? (← getEnv) key).isSome then return
  let .const c _ := key.getAppFn | throwError "unit key {key} is not a constant application"
  let isFn : Bool ← forallTelescope (← inferType key) fun xs _ => pure (decide (xs.size > 0))
  if ← isRecursiveDef c then
    -- the unfolding equation first; for well-founded definitions whose recursive
    -- calls we cannot prove decreasing, the functional (with Lean's own proofs)
    let saved ← saveState
    try translateRecursive key extra
    catch e =>
      let msg ← e.toMessageData.toString
      unless (msg.splitOn "cannot prove the recursive call decreases").length > 1 do throw e
      saved.restore
      translateRecursive key extra (functional := true)
  else if isFn then translateFunction key extra
  else translateThunk key extra

/-- Translate `key`, first translating (recursively) the units it needs.
Units needed only after unfolding (not visible in the body) are added to the
dependencies explicitly (`extra`). -/
partial def translateUnit (key : Expr) (stack : List Expr := []) (extra : Array Expr := #[]) :
    MetaM Unit := do
  if (getUnit? (← getEnv) key).isSome then return
  if stack.contains key then throwError "cyclic unit dependency at {key} (mutual recursion is not supported yet)"
  if stack.length > 200 then throwError "unit dependency chain too deep at {key}"
  let saved ← saveState
  needUnitRef.set none
  try
    let t0 ← IO.monoMsNow
    let nm := (← ppExpr key).pretty.take 120
    cakeLog s!"[cake] start unit {nm}"
    withCurrHeartbeats (translateUnitOnce key extra)
    cakeLog s!"[cake] {(← IO.monoMsNow) - t0}ms unit {nm}"
  catch e =>
    match ← needUnitRef.get with
    | some dep =>
      saved.restore
      needUnitRef.set none
      if extra.contains dep then
        throwError "while translating {key}: unit {dep} is in scope but still needed: {e.toMessageData}"
      translateUnit dep (key :: stack)
      translateUnit key stack (extra.push dep)
    | none =>
      saved.restore
      throwError "while translating {key}: {e.toMessageData}"

end ConPastel.Translator.Meta
