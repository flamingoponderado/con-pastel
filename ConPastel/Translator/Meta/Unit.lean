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
  (for each dependency d) ∀ v_d,
    nsLookup (buildRecEnv funs envC envC.v) (.short n_d) = some v_d →
    INV d v_d →
  INV u (recclosure envC funs nᵤ)
```

A dependency's value is arbitrary: it may be a closure of the same group or
of an earlier `Dletrec` (when `cake_program` splits the units into groups).

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

/-- `nsLookup (buildRecEnv funs envC envC.v) (.short n) = some v` -/
def groupLookupTyV (envC funs : Expr) (n : String) (v : Expr) : MetaM Expr := do
  let ns ← mkAppM ``buildRecEnv #[funs, envC, ← mkAppM ``SemEnv.v #[envC]]
  mkEq (← mkAppM ``nsLookup #[ns, shortIdent n]) (← mkAppM ``Option.some #[v])

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
      withLocalDeclD `vd (mkConst ``Value) fun value => do
      withLocalDeclD `hl (← groupLookupTyV envC funs u.cname value) fun hl => do
      withLocalDeclD `hv (mkApp2 inv tgt value) fun hv => do
        go ds (acc ++ #[value, hl, hv]) (globals.insert d { cname := u.cname, value, inv, cert := hv })
  go deps.toList #[] {}

/-- Finish a unit: name the body, state and check the certificate, register. -/
def finishUnit (key : Expr) (uname : Name) (cname : String) (kind : UnitKind) (deps : Array Expr)
    (body : Expr) (hyps : Array Expr) (envC funs : Expr) (pf : Expr) (target inv : Expr)
    (peers : Array Name := #[]) : MetaM Unit := do
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
  addUnit { key, name := uname, cname, kind, cert := uname ++ `cert, datatypes, deps, assumes, depNames, peers }

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

/-- A well-founded definition's termination argument: a `Nat` measure
(`WellFounded.Nat.fix`) or a relation with its well-foundedness proof. -/
inductive WfSpec where
  | nat (m : Expr)
  | gen (r hwf : Expr)
  deriving Inhabited

/-- The parts of a well-founded definition's unfolding `v` (its value applied
to the arguments): `c._unary fixed packed` or (one varying argument)
`WellFounded.Nat.fix … packed`. Returns `(fixed, packed, α, motive, measure, F)`. -/
def wfParts (c : Name) (v : Expr) : MetaM (Option (Array Expr × Expr × Expr × Expr × WfSpec × Expr)) := do
  let some info := Lean.Elab.WF.eqnInfoExt.find? (← getEnv) c | return none
  let ofFix (fixed : Array Expr) (u packed : Expr) : Option (Array Expr × Expr × Expr × Expr × WfSpec × Expr) :=
    match u.getAppFnArgs with
    | (``WellFounded.Nat.fix, #[α, motive, m, F]) => some (fixed, packed, α, motive, .nat m, F)
    | (``WellFounded.fix, #[α, motive, r, hwf, F]) => some (fixed, packed, α, motive, .gen r hwf, F)
    | _ => none
  if let .const un ulvls := v.getAppFn then
    if un == info.declNameNonRec then
      let fixed := v.getAppArgs.pop
      let u := (mkAppN (← instantiateValueLevelParams (← getConstInfo un) ulvls) fixed).headBeta
      return ofFix fixed u v.getAppArgs.back!
  if v.isAppOfArity ``WellFounded.Nat.fix 5 || v.isAppOfArity ``WellFounded.fix 6 then
    return ofFix #[] v.appFn! v.appArg!
  return none

/-- The well-founded relation of a recursion over `τ` given the packing `pk`
of a `τ` value into Lean's own recursion domain: a measure, or the inverse
image of Lean's relation. Returns `(r, wf)`. -/
def wfRelOver (τ : Expr) (pk : Expr → MetaM (Expr × WfSpec)) : MetaM (Expr × Expr) := do
  let (spec0, isNat, fiber) ← withLocalDeclD `p τ fun p => do
    let (_, sp) ← pk p
    match sp with
    | .nat _ => pure (sp, true, none)
    | .gen r hwf =>
      if r.hasFVar || hwf.hasFVar then
        -- the relation mentions the (fixed) parameters: relate tuples with the
        -- same relation, by that relation (`wf_fiber`)
        let rP ← mkLambdaFVars #[p] r
        let hP ← mkLambdaFVars #[p] hwf
        if rP.hasFVar || hP.hasFVar then
          throwError "a well-founded relation depending on outer variables is not supported"
        pure (sp, false, some (rP, hP))
      else pure (sp, false, none)
  if let some (rP, hP) := fiber then
    let pkF ← withLocalDeclD `p τ fun p => do mkLambdaFVars #[p] (← pk p).1
    let rel ← withLocalDeclD `a τ fun a => withLocalDeclD `b τ fun b => do
      let ra := (rP.beta #[a]).headBeta
      let rb := (rP.beta #[b]).headBeta
      mkLambdaFVars #[a, b] (mkAnd (← mkEq ra rb) (mkApp2 rb (pkF.beta #[a]).headBeta (pkF.beta #[b]).headBeta))
    return (rel, ← mkAppOptM ``ConPastel.Translator.wf_fiber #[none, none, rP, pkF, hP])
  if isNat then
    let msr ← withLocalDeclD `p τ fun p => do
      let (packed, sp) ← pk p
      let .nat m := sp | unreachable!
      mkLambdaFVars #[p] (m.beta #[packed]).headBeta
    let wfr ← mkAppOptM ``measure #[τ, msr]
    return (← mkAppOptM ``WellFoundedRelation.rel #[τ, wfr], ← mkAppOptM ``WellFoundedRelation.wf #[τ, wfr])
  let .gen r hwf := spec0 | unreachable!
  let pkF ← withLocalDeclD `p τ fun p => do mkLambdaFVars #[p] (← pk p).1
  return (← mkAppOptM ``InvImage #[none, none, r, pkF], ← mkAppOptM ``InvImage.wf #[none, none, r, pkF, hwf])

/-- The termination relation of a recursive unit over the tuple type `τ` of
its arguments: `sizeOf` of the structural argument, or Lean's own
termination argument (measure or relation) for a `termination_by` definition. -/
def recursionRel (key : Expr) (c : Name) (static : Array Expr) (n : Nat) (τ : Expr) : MetaM (Expr × Expr) := do
  let env ← getEnv
  if (Lean.Elab.WF.eqnInfoExt.find? env c).isSome then
    wfRelOver τ fun p => do
      let projs ← tupleProjs p n
      let v := (mkAppN (← keyValue key) projs.toArray).headBeta
      let some (_, packed, _, _, sp, _) ← wfParts c v
        | throwError "{c}: well-founded recursion of this shape is not supported yet: {v}"
      pure (packed, sp)
  else
    let some k ← structRecArg? c | throwError "{c}: no recursion information"
    let msr ← withLocalDeclD `p τ fun p => do
      let comp := (← tupleProjs p n)[k - static.size]!
      mkLambdaFVars #[p] (← mkAppM ``SizeOf.sizeOf #[comp])
    let wfr ← mkAppOptM ``measure #[τ, msr]
    return (← mkAppOptM ``WellFoundedRelation.rel #[τ, wfr], ← mkAppOptM ``WellFoundedRelation.wf #[τ, wfr])

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
  let some (_, packed, α, motive, sp, F) ← wfParts c v | return none
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
  let pf ← match sp with
    | .nat m => mkAppOptM ``WellFounded.Nat.fix_eq #[α, motive, m, F, packed]
    | .gen r hwf => mkAppOptM ``WellFounded.fix_eq #[α, motive, r, hwf, F, packed]
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
  let (r, hwf) ← recursionRel key c static n τ
  let body ← mkFreshExprMVar (mkConst ``Exp)
  let inv ← if dep then mkAppM ``DARROW #[invT, invBf] else mkAppM ``Arrow #[invT, invBf.bindingBody!]
  withGroupHyps cname param body deps fun envC funs hnodup hfind hyps gctx₀ => do
    let cl ← mkAppM ``Value.recclosure #[envC, funs, mlString cname]
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

/-- The members of `c`'s well-founded mutual block (`#[]` if not mutual). -/
def mutualMembers (c : Name) : MetaM (Array Name) := do
  match Lean.Elab.WF.eqnInfoExt.find? (← getEnv) c with
  | some info => return if info.declNames.size > 1 then info.declNames else #[]
  | none => return #[]

/-- The hypotheses of a mutual block's certificates: for every member its
entry (`hfind`) and lookup (`hself`), then the common ones. `k` gets `envC`,
`funs`, `hnodup`, the entries, the lookups, the common hypotheses
(`hbool hlist hcs…`), the assumptions, the dependency hypotheses and the context. -/
def withBlockHyps {α : Type} [Inhabited α] (members : Array (String × String × Expr)) (deps : Array Expr)
    (k : Expr → Expr → Expr → Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → GCtx → MetaM α) :
    MetaM α := do
  withLocalDeclD `envC (mkApp (mkConst ``SemEnv) (mkConst ``Value)) fun envC => do
  let fty ← funTy
  withLocalDeclD `funs (← mkAppM ``List #[fty]) fun funs => do
  let nodupTy ← mkAppM ``List.Nodup #[← mkAppM ``List.map #[← withLocalDeclD `p fty fun p => do
    mkLambdaFVars #[p] (← mkAppM ``Prod.fst #[p]), funs]]
  withLocalDeclD `hnodup nodupTy fun hnodup => do
  let findTys ← members.mapM fun (self, param, body) => do
    mkEq (← mkAppM ``findRecFun #[mlString self, funs]) (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[mlString param, body]])
  withLocalDeclsDND (findTys.map (`hfind, ·)) fun hfinds => do
  let envCc ← mkAppM ``SemEnv.c #[envC]
  withLocalDeclD `hbool (← mkAppM ``HasBoolCons #[envCc]) fun hbool => do
  withLocalDeclD `hlist (← mkAppM ``HasListCons #[envCc]) fun hlist => do
  let dts := (datatypeExt.getState (← getEnv)).toList.map (·.1)
  withLocalDeclsDND (dts.toArray.map fun T => (`hc, mkApp (mkConst (T ++ `cakeHasCons)) envCc)) fun hcs => do
  let hasCons : NameMap Expr := (dts.zip hcs.toList).foldl (fun m (T, h) => m.insert T h) {}
  let selfTys ← members.mapM fun (self, _, _) => groupLookupTy envC funs self
  withLocalDeclsDND (selfTys.map (`hself, ·)) fun hselfs => do
  let reps := assumeReplaceExt.getState (← getEnv)
  withLocalDeclsDND (reps.map fun (_, _, P) => (`ha, P)) fun has => do
  let assumed := (reps.zip has).map fun ((k, r, _), h) => (k, r, h)
  let rec go : List Expr → Array Expr → Std.HashMap Expr GlobalVar → MetaM α
    | [], acc, globals =>
      k envC funs hnodup hfinds hselfs (#[hbool, hlist] ++ hcs) has acc
        { hbool, hlist, hasCons, globals, unfoldRec := false, assumed }
    | d :: ds, acc, globals => do
      let some u := getUnit? (← getEnv) d | throwError "unit {d} missing"
      let (tgt, inv) ← unitTarget u
      withLocalDeclD `vd (mkConst ``Value) fun value => do
      withLocalDeclD `hl (← groupLookupTyV envC funs u.cname value) fun hl => do
      withLocalDeclD `hv (mkApp2 inv tgt value) fun hv => do
        go ds (acc ++ #[value, hl, hv]) (globals.insert d { cname := u.cname, value, inv, cert := hv })
  go deps.toList #[] {}

/-- Case analysis on a nested sum `τ₀ ⊕' (τ₁ ⊕' …)` with a non-dependent result:
`alt i t` for the `i`-th summand. -/
partial def sumCasesND (tys : List Expr) (res : Expr) (alt : Nat → Expr → MetaM Expr) (s : Expr) (i : Nat := 0) :
    MetaM Expr := do
  match tys with
  | [] => throwError "empty sum"
  | [_] => alt i s
  | τ :: rest =>
    let restTy ← sumTy rest
    let motive ← withLocalDeclD `x (← mkAppM ``PSum #[τ, restTy]) fun x => mkLambdaFVars #[x] res
    let l ← withLocalDeclD `t τ fun t => do mkLambdaFVars #[t] (← alt i t)
    let r ← withLocalDeclD `s restTy fun s' => do mkLambdaFVars #[s'] (← sumCasesND rest res alt s' (i + 1))
    mkAppOptM ``PSum.casesOn #[τ, restTy, motive, s, l, r]
where
  sumTy : List Expr → MetaM Expr
    | [] => throwError "empty sum"
    | [τ] => pure τ
    | τ :: rest => do mkAppM ``PSum #[τ, ← sumTy rest]

/-- The nested sum type `τ₀ ⊕' (τ₁ ⊕' …)`. -/
def sumTyOf (tys : List Expr) : MetaM Expr := sumCasesND.sumTy tys

/-- The injection of the `i`-th summand. -/
partial def sumInj (tys : List Expr) (i : Nat) (t : Expr) : MetaM Expr := do
  match tys, i with
  | [_], _ => pure t
  | τ :: rest, 0 => mkAppOptM ``PSum.inl #[τ, ← sumTyOf rest, t]
  | τ :: rest, i + 1 => mkAppOptM ``PSum.inr #[τ, ← sumTyOf rest, ← sumInj rest i t]
  | [], _ => throwError "empty sum"

/-- Dependent case analysis for the joint induction step: for the `i`-th
summand, `alt i t ih` proves `C (ctx (inj t))` from the induction hypothesis at
`ctx (inj t)`; the result proves `(∀ y, r y s → Pred y) → Pred s`. -/
partial def sumCasesStep (tys : List Expr) (C : Expr → MetaM Expr) (ihTyAt : Expr → MetaM Expr)
    (ctx : Expr → MetaM Expr) (alt : Nat → Expr → Expr → MetaM Expr) (s : Expr) (i : Nat := 0) : MetaM Expr := do
  match tys with
  | [] => throwError "empty sum"
  | [τ] =>
    let _ := τ
    withLocalDeclD `ih (← ihTyAt (← ctx s)) fun ih => do mkLambdaFVars #[ih] (← alt i s ih)
  | τ :: rest =>
    let restTy ← sumTyOf rest
    let sty ← mkAppM ``PSum #[τ, restTy]
    let motive ← withLocalDeclD `x sty fun x => do
      let cx ← ctx x
      mkLambdaFVars #[x] (← mkArrow (← ihTyAt cx) (← C cx))
    let l ← withLocalDeclD `t τ fun t => do
      let ct ← ctx (← mkAppOptM ``PSum.inl #[τ, restTy, t])
      withLocalDeclD `ih (← ihTyAt ct) fun ih => do mkLambdaFVars #[t, ih] (← alt i t ih)
    let ctx' (x : Expr) : MetaM Expr := do ctx (← mkAppOptM ``PSum.inr #[τ, restTy, x])
    let r ← withLocalDeclD `s restTy fun s' => do
      mkLambdaFVars #[s'] (← sumCasesStep rest C ihTyAt ctx' alt s' (i + 1))
    mkAppOptM ``PSum.casesOn #[τ, sty.appArg!, motive, s, l, r]

/-- The constants used by `es` (transitively) that are missing from `env0`, in
dependency order: the auxiliary declarations (e.g. `_proof_i_j`) a solve running in
another thread added to its own copy of the environment. -/
partial def newConstsSince (env0 : Environment) (es : Array Expr) : MetaM (Array ConstantInfo) := do
  let env ← getEnv
  let seen ← IO.mkRef (∅ : NameSet)
  let out ← IO.mkRef (#[] : Array ConstantInfo)
  let rec go (n : Name) : MetaM Unit := do
    if env0.contains n || (← seen.get).contains n then return
    seen.modify (·.insert n)
    let some ci := env.find? n | throwError "newConstsSince: unknown constant {n}"
    for m in ci.type.getUsedConstants do go m
    if let some v := ci.value? (allowOpaque := true) then
      for m in v.getUsedConstants do go m
    out.modify (·.push ci)
  for e in es do
    for n in e.getUsedConstants do go n
  out.get

/-- Add constants collected by `newConstsSince` to the environment. -/
def addConstInfos (cis : Array ConstantInfo) : MetaM Unit := do
  for ci in cis do
    if (← getEnv).contains ci.name then continue
    match ci with
    | .thmInfo v => addDecl (.thmDecl v)
    | .defnInfo v => addDecl (.defnDecl v)
    | .opaqueInfo v => addDecl (.opaqueDecl v)
    | _ => throwError "addConstInfos: unexpected constant kind for {ci.name}"

/-- Member proofs kept across the retries of a parallel round: a round that
needed more units still solved most members, in a context that the retry only
extends (more dependency hypotheses). The context is recorded so the proofs can
be moved into the retry's (fresh) local variables; types are compared after the
move, and a member is re-solved if anything does not match. -/
structure MutCache where
  block : Array Name
  cnames : Array String
  unames : Array Name
  fixed : Array Expr
  fixedTys : Array (Option Expr)
  deps : Array Expr
  depFVars : Array Expr
  depTys : Array Expr
  pih : Array (Option (Expr × Expr × Expr × Expr))
  results : Array (Option (Expr × Expr × Array ConstantInfo))
  deriving Inhabited

initialize mutualCacheRef : IO.Ref (Option MutCache) ← IO.mkRef none

/-- Rename string literals (the members' CakeML names, which shift when a retry
translates further units first). -/
def renameStrLits (m : Array (String × String) × Array (Name × Name)) (e : Expr) : Expr :=
  if m.1.isEmpty && m.2.isEmpty then e else e.replace fun x => match x with
    | .lit (.strVal s) => (m.1.find? (·.1 == s)).map fun (_, t) => .lit (.strVal t)
    | .const n ls => (m.2.find? (·.1 == n)).map fun (_, t) => .const t ls
    | _ => none
initialize mutualRoundRef : IO.Ref Nat ← IO.mkRef 0

/-- A well-founded mutual block: all members translated together, by one
well-founded induction over the sum of their argument tuples. -/
def translateMutual (members : Array Name) (extra : Array Expr) : MetaM Unit := do
  for m in members do
    unless (← getConstInfo m).levelParams.isEmpty do throwError "mutual block member {m} is universe polymorphic"
  let keys := members.map (mkConst ·)
  -- equations and dependencies
  let eqns ← members.mapM fun c => do
    let some e ← getUnfoldEqnFor? c (nonRec := true) | throwError "no unfold equation for {c}"
    pure e
  let mut deps := extra
  for i in [0:members.size] do
    let ds ← forallTelescope (← inferType keys[i]!) fun xs _ => do
      unitDepsOf keys[i]! (← inferType (mkAppN (mkConst eqns[i]!) xs))
    deps := mergeDeps ds deps
  deps := deps.filter fun d => !keys.contains d
  cakeLog s!"[mutual] {members.size} members, {deps.size} dependencies"
  -- per member: arity, tuple type, result type, invariants, names
  let k0 := unitCount (← getEnv)
  let mut infos : Array (Nat × Expr × Expr × Name × String) := #[]
  for i in [0:members.size] do
    let (n, tys, resTy) ← forallTelescope (← inferType keys[i]!) fun xs resTy => do
      let tys ← xs.mapM inferType
      if tys.any (·.hasFVar) || resTy.hasFVar then
        throwError "{members[i]!}: dependent types in a mutual block are not supported yet"
      return (xs.size, tys, resTy)
    let τ ← tupleTy tys.toList
    let env ← getEnv
    let (uname, cname) := match cakeTagExt.getState env with
      | some t => (Name.mkStr (unitNamespace env) s!"u{k0 + i}", s!"%{t}.{k0 + i}")
      | none => (Name.mkStr `ConPastel.Cake s!"u{k0 + i}", s!"%{k0 + i}")
    infos := infos.push (n, τ, resTy, uname, cname)
  let taus := infos.toList.map (·.2.1)
  let S ← sumTyOf taus
  let param := "p"
  cakeLog s!"[mutual] sum type built"
  -- tupled functions and invariants
  let mut fts : Array Expr := #[]
  let mut invTs : Array Expr := #[]
  let mut invBs : Array Expr := #[]
  for i in [0:members.size] do
    let (n, τ, resTy, uname, _) := infos[i]!
    invTs := invTs.push (← invOf τ)
    invBs := invBs.push (← invOf resTy)
    if n > 1 then
      let tupName := uname ++ `tupled
      -- a split block's parts and its finish import the one from `prepare`
      unless (← getEnv).contains tupName do
        let tupVal ← withLocalDeclD `p τ fun p => do mkLambdaFVars #[p] (mkAppN keys[i]! (← tupleProjs p n).toArray)
        addDecl (Declaration.defnDecl (mkDefinitionValEx tupName [] (← mkArrow τ resTy) tupVal .abbrev .safe []))
      fts := fts.push (mkConst tupName)
    else fts := fts.push keys[i]!
  let split : Option SplitMode := (← mutualSplitRef.get).bind fun (t, m) => if members.contains t then some m else none
  if let some .prepare := split then
    cakeLog s!"[split] prepared {members.size} members, {deps.size} dependencies"
    return
  -- the joint termination relation: Lean's own (`_mutual`), through each summand's packing
  let partsAt (i : Nat) (t : Expr) : MetaM (Expr × Expr × WfSpec) := do
    let (n, _, _, _, _) := infos[i]!
    let v := (mkAppN (← keyValue keys[i]!) (← tupleProjs t n).toArray).headBeta
    let some (_, packed, α, _, sp, _) ← wfParts members[i]! v
      | throwError "{members[i]!}: unexpected well-founded definition shape {v}"
    pure (packed, α, sp)
  let (α, isNat) ← withLocalDeclD `t infos[0]!.2.1 fun t => do
    let (_, α, sp) ← partsAt 0 t
    pure (α, match sp with | .nat _ => true | .gen .. => false)
  let (r, hwf) ← if isNat then do
      let M ← withLocalDeclD `s S fun s => do
        mkLambdaFVars #[s] (← sumCasesND taus (mkConst ``Nat) (fun i t => do
          let (packed, _, sp) ← partsAt i t
          let .nat m := sp | throwError "mixed termination arguments in a mutual block"
          pure (m.beta #[packed]).headBeta) s)
      let wfr ← mkAppOptM ``measure #[S, M]
      pure (← mkAppOptM ``WellFoundedRelation.rel #[S, wfr], ← mkAppOptM ``WellFoundedRelation.wf #[S, wfr])
    else do
      let (r', hwf') ← withLocalDeclD `t infos[0]!.2.1 fun t => do
        let (_, _, sp) ← partsAt 0 t
        let .gen r' hwf' := sp | throwError "mixed termination arguments in a mutual block"
        if r'.hasFVar || hwf'.hasFVar then throwError "a well-founded relation depending on the arguments is not supported yet"
        pure (r', hwf')
      let repack ← withLocalDeclD `s S fun s => do
        mkLambdaFVars #[s] (← sumCasesND taus α (fun i t => do pure (← partsAt i t).1) s)
      pure (← mkAppOptM ``InvImage #[none, none, r', repack], ← mkAppOptM ``InvImage.wf #[none, none, r', repack, hwf'])
  cakeLog s!"[mutual] termination relation built"
  let bodies ← members.mapM fun _ => mkFreshExprMVar (mkConst ``Exp)
  let memberSpecs := (List.range members.size).toArray.map fun i => (infos[i]!.2.2.2.2, param, bodies[i]!)
  withBlockHyps memberSpecs deps fun envC funs hnodup hfinds hselfs common has depHyps gctx₀ => do
    let cls ← infos.mapM fun (_, _, _, _, cname) => mkAppM ``Value.recclosure #[envC, funs, mlString cname]
    -- the member statements and the joint predicate
    let P (i : Nat) (t : Expr) : MetaM Expr := do
      withLocalDeclD `v (mkConst ``Value) fun v => do
        mkForallFVars #[v] (← mkArrow (mkApp2 invTs[i]! t v)
          (← mkAppM ``AppReturns #[cls[i]!, v, mkApp invBs[i]! (mkApp fts[i]! t)]))
    let Pred ← withLocalDeclD `s S fun s => do mkLambdaFVars #[s] (← sumCasesND taus (mkSort .zero) P s)
    let PredAt (x : Expr) : MetaM Expr := pure (Pred.beta #[x]).headBeta
    let ihTyAt (x : Expr) : MetaM Expr := withLocalDeclD `y S fun y => do
      mkForallFVars #[y] (← mkArrow (mkApp2 r y x) (← PredAt y))
    let bms : Array BlockMember ← (List.range members.size).toArray.mapM fun i => do
      let inj ← withLocalDeclD `t infos[i]!.2.1 fun t => do mkLambdaFVars #[t] (← sumInj taus i t)
      pure { head := members[i]!, arity := infos[i]!.1, cl := cls[i]!, cname := infos[i]!.2.2.2.2, inj,
             invT := invTs[i]!, invB := invBs[i]!, ft := fts[i]! }
    -- one member's case of the induction step: `∀ pv, invT p pv → AppReturns …`,
    -- in the local context of the case split (`p`, `ih`); also returns the body
    let solveMember (i : Nat) (p ih : Expr) (collect : Bool := false) : MetaM (Expr × Expr) := do
      let (n, _, _, _, cname) := infos[i]!
      withLocalDeclD `pv (mkConst ``Value) fun pv => do
      withLocalDeclD `hp (mkApp2 invTs[i]! p pv) fun hp => do
        let env ← bodyEnv envC funs param pv
        let g ← mkFreshExprMVar (← mkAppM ``Eval #[env, bodies[i]!, mkApp invBs[i]! (mkApp fts[i]! p)])
        let mr : MutRec := { members := bms, ih, s := ← sumInj taus i p, r }
        let gctx := { gctx₀ with mrec? := some mr, collectNeeds := collect }
        let gst : GSt := { locals := #[{ fvar := p, cname := param, value := pv, rel := hp }] }
        let eqnApp (as : Array Expr) : MetaM Expr := pure (mkAppN (mkConst eqns[i]!) as)
        let t0 ← IO.monoMsNow
        let _ ← (destructAndSolve g.mvarId! env (fun _ => pure invBs[i]!) keys[i]! eqnApp #[] p n).run gst |>.run gctx
        cakeLog s!"[mutual] member {i} {members[i]!} solved in {(← IO.monoMsNow) - t0}ms"
        let app ← withTransparency .all <| mkAppOptM ``AppReturns_recclosure #[envC, funs, mlString cname,
          mlString param, bodies[i]!, pv, mkApp invBs[i]! (mkApp fts[i]! p), hnodup, hfinds[i]!, g]
        pure (← instantiateMVars bodies[i]!, ← instantiateMVars (← mkLambdaFVars #[pv, hp] app))
    let sequentialStep : MetaM Expr := withLocalDeclD `s S fun s => do
      let pf ← sumCasesStep taus PredAt ihTyAt pure (fun i p ih => do pure (← solveMember i p ih).2) s
      mkLambdaFVars #[s] pf
    -- split translation: a member's case as a closed theorem `u.step` over the
    -- block's hypotheses (without the other members' entries, whose bodies a
    -- part does not know) and its case variables `p`, `ih`
    let memberTy (i : Nat) (p : Expr) : MetaM Expr := withLocalDeclD `pv (mkConst ``Value) fun pv => do
      mkForallFVars #[pv] (← mkArrow (mkApp2 invTs[i]! p pv)
        (← mkAppM ``AppReturns #[cls[i]!, pv, mkApp invBs[i]! (mkApp fts[i]! p)]))
    let ctxOf (i : Nat) : Array Expr :=
      #[envC, funs, hnodup, hfinds[i]!] ++ common ++ hselfs ++ has ++ depHyps
    let unameOf (i : Nat) : Name := infos[i]!.2.2.2.1
    if let some (.part j n) := split then
      let mine := (List.range members.size).filter (· % n == j)
      cakeLog s!"[split] part {j}/{n}: members {mine}"
      -- distinct auxiliary-declaration names in every part (they are imported together)
      let dg ← getDeclNGen
      setDeclNGen { dg with idx := dg.idx + (j + 1) * 1000000 }
      let clearNeeds : MetaM Unit := do
        needUnitsAllRef.set #[]; needDatatypesAllRef.set #[]
        needUnitRef.set none; pendingUnitsRef.set #[]; needDatatypeRef.set none
      clearNeeds
      let out ← IO.mkRef (#[] : Array (Nat × Expr × Expr × Expr))
      try
        let _ ← withLocalDeclD `s S fun s => do
          sumCasesStep taus PredAt ihTyAt pure (fun i p ih => do
            let ty ← memberTy i p
            if mine.contains i then
              let (b, pf) ← solveMember i p ih (collect := true)
              let fvs := ctxOf i ++ #[p, ih]
              out.modify (·.push (i, b, ← instantiateMVars (← mkForallFVars fvs ty),
                ← instantiateMVars (← mkLambdaFVars fvs pf)))
            mkSorry ty false) s
      catch e =>
        -- no retry here: units or datatypes added by one part would not be in the others
        clearNeeds
        throwError "cake_mutual_part {j}/{n}: {e.toMessageData}"
      let dedup (xs : Array Expr) : Array Expr := xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]
      let dts := dedup (← needDatatypesAllRef.get)
      let units := dedup (← needUnitsAllRef.get)
      clearNeeds
      if dts.size + units.size > 0 then
        throwError "cake_mutual_part {j}/{n}: the block needs units {units.map toString} and datatypes {dts.map toString}; translate them in `cake_mutual_prepare` (list the units after the block's name)"
      for (i, b, stTy, stPf) in (← out.get) do
        if b.hasMVar || b.hasFVar || stTy.hasMVar || stTy.hasFVar || stPf.hasMVar || stPf.hasFVar || stPf.hasSorry then
          throwError "cake_mutual_part {j}/{n}: member {i} ({members[i]!}): its step has metavariables, free variables or sorry"
        addDecl (Declaration.defnDecl (mkDefinitionValEx (unameOf i ++ `mbody) [] (mkConst ``Exp) b .abbrev .safe []))
        addDecl (Declaration.thmDecl (mkTheoremValEx (unameOf i ++ `step) [] stTy stPf []))
      cakeLog s!"[split] part {j}/{n}: {mine.length} members done"
      return
    -- the members' cases are independent: solve them in parallel threads
    -- (`CAKE_PAR` workers, default 8; `CAKE_PAR=1` is the sequential translation).
    -- Each case is first a placeholder in the case split, then filled with the
    -- thread's closed result. Any failure reruns sequentially, so errors and
    -- need-unit/need-datatype requests are reported exactly as before.
    let par := ((← IO.getEnv "CAKE_PAR").bind String.toNat?).getD 8
    -- split translation, finish: every member's case from its part
    let finishStep : MetaM Expr := do
      for i in [0:members.size] do
        let some (.defnInfo v) := (← getEnv).find? (unameOf i ++ `mbody)
          | throwError "cake_mutual_finish: no part result for member {i} ({members[i]!}); is its `cake_mutual_part` module imported?"
        bodies[i]!.mvarId!.assign v.value
      let skel ← withLocalDeclD `s S fun s => do
        let pf ← sumCasesStep taus PredAt ihTyAt pure (fun i p ih => do
          let app := mkAppN (mkConst (unameOf i ++ `step)) (ctxOf i ++ #[p, ih])
          let want ← instantiateMVars (← memberTy i p)
          let got ← instantiateMVars (← inferType app)
          unless got == want do
            throwError "cake_mutual_finish: the part result for member {i} ({members[i]!}) does not match the block (rebuild its part)"
          pure app) s
        mkLambdaFVars #[s] pf
      instantiateMVars skel
    let step ← if let some .finish := split then finishStep else if par ≤ 1 then sequentialStep else do
      let saved ← saveState
      -- the context, for moving proofs between rounds
      let fixed := #[envC, funs, hnodup] ++ hfinds ++ common ++ hselfs ++ has
      let fixedTys ← fixed.mapIdxM fun j x => do
        -- the entries mention the members' bodies (metavariables): not compared
        if j ≥ 3 && j < 3 + hfinds.size then pure none
        else pure (some (← instantiateMVars (← inferType x)))
      let depTys ← depHyps.mapM fun x => do instantiateMVars (← inferType x)
      let cache? := (← mutualCacheRef.get).filter (·.block == members)
      mutualCacheRef.set none
      -- the base substitution (old context ↦ this one), if the contexts match
      let cnamesNow := infos.map (·.2.2.2.2)
      let unamesNow := infos.map (·.2.2.2.1)
      -- the members' CakeML names and unit constants (`u_k`, `u_k.tupled`, …)
      let ren : Array (String × String) × Array (Name × Name) := match cache? with
        | some c => ((c.cnames.zip cnamesNow).filter fun (a, b) => a != b,
            ((c.unames.zip unamesNow).filter fun (a, b) => a != b).flatMap fun (a, b) =>
              #[(a, b), (a ++ `tupled, b ++ `tupled), (a ++ `body, b ++ `body)])
        | none => (#[], #[])
      let base? : Option (Array Expr × Array Expr) ← do
        let some c := cache? | pure none
        if c.fixed.size != fixed.size || c.depFVars.size != 3 * c.deps.size then
          cakeLog s!"[mutual] previous round not reusable: context size {c.fixed.size} vs {fixed.size}"
          pure none else
        let mut olds := c.fixed
        let mut news := fixed
        let mut okDeps := true
        for j in [0:c.deps.size] do
          match deps.findIdx? (· == c.deps[j]!) with
          | some j' =>
            olds := olds ++ c.depFVars.extract (3 * j) (3 * j + 3)
            news := news ++ depHyps.extract (3 * j') (3 * j' + 3)
          | none => okDeps := false
        if !okDeps then
          cakeLog s!"[mutual] previous round not reusable: a dependency is gone"
          pure none else
        let mut okTys := true
        for j in [0:fixed.size] do
          if let (some o, some n) := (c.fixedTys[j]!, fixedTys[j]!) then
            if (renameStrLits ren o).replaceFVars olds news != n then
              okTys := false
              cakeLog s!"[mutual] previous round not reusable: hypothesis {j} type differs" 
        for j in [0:c.deps.size] do
          if let some j' := deps.findIdx? (· == c.deps[j]!) then
            for t in [0:3] do
              if (renameStrLits ren c.depTys[3 * j + t]!).replaceFVars olds news != depTys[3 * j' + t]! then
                okTys := false
                cakeLog s!"[mutual] previous round not reusable: dependency {j} hypothesis {t} type differs" 
        pure (if okTys then some (olds, news) else none)
      -- distinct auxiliary-declaration names in every round (kept proofs carry theirs)
      let round ← mutualRoundRef.modifyGet fun r => (r, r + 1)
      let dg ← getDeclNGen
      setDeclNGen { dg with idx := dg.idx + (round + 1) * (members.size + 1) }
      let jobs ← IO.mkRef (#[] : Array (Nat × MVarId × (Unit → EIO Exception (Expr × Expr × Array ConstantInfo))))
      let reused ← IO.mkRef (#[] : Array (Nat × Expr × Expr × Array ConstantInfo))
      let pihs ← IO.mkRef (Array.replicate members.size (none : Option (Expr × Expr × Expr × Expr)))
      let skel ← withLocalDeclD `s S fun s => do
        let pf ← sumCasesStep taus PredAt ihTyAt pure (fun i p ih => do
          let ty ← withLocalDeclD `pv (mkConst ``Value) fun pv => do
            mkForallFVars #[pv] (← mkArrow (mkApp2 invTs[i]! p pv)
              (← mkAppM ``AppReturns #[cls[i]!, pv, mkApp invBs[i]! (mkApp fts[i]! p)]))
          let ph ← mkFreshExprSyntheticOpaqueMVar ty
          let pTy ← instantiateMVars (← inferType p)
          let ihTy ← instantiateMVars (← inferType ih)
          pihs.modify (·.set! i (some (p, ih, pTy, ihTy)))
          -- a proof kept from the previous round, moved into this context
          let kept ← do
            let (some (olds, news), some c) := (base?, cache?) | pure none
            let (some (b, opf, aux), some (op, oih, opTy, oihTy)) := (c.results[i]?.join, c.pih[i]?.join) | pure none
            let olds := olds ++ #[op, oih]
            let news := news ++ #[p, ih]
            if (renameStrLits ren opTy).replaceFVars olds news != pTy ||
                (renameStrLits ren oihTy).replaceFVars olds news != ihTy then
              cakeLog s!"[mutual] member {i}: argument or induction hypothesis type differs"
              pure none
            else pure (some (renameStrLits ren b, (renameStrLits ren opf).replaceFVars olds news, aux))
          -- a kept proof is kernel-checked on its own (in a worker) before it is
          -- used; if that fails, the member is solved afresh
          let otherFinds := ((List.range members.size).filter (· != i)).toArray.map (hfinds[·]!)
          let keptOk (b pf : Expr) (aux : Array ConstantInfo) : MetaM Bool := do
            let s0 ← saveState
            let ok ← try
                addConstInfos aux
                bodies[i]!.mvarId!.assign b
                let fvs := (← getLCtx).getFVars.filter fun x => !otherFinds.contains x
                let ty' ← instantiateMVars (← mkForallFVars fvs ty)
                let val ← instantiateMVars (← mkLambdaFVars fvs pf)
                if ty'.hasMVar || val.hasMVar || val.hasSorry then pure false else
                match Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions)
                    (.thmDecl (mkTheoremValEx `_cake_keep_check [] ty' val [])) with
                | .ok _ => pure true
                | .error _ => pure false
              catch _ => pure false
            s0.restore
            pure ok
          if kept.isSome then reused.modify (·.push (i, default, default, #[]))
          let mctx ← readThe Meta.Context
          let mst ← getThe Meta.State
          let env0 ← getEnv
          let job : MetaM (Expr × Expr × Array ConstantInfo) := do
              if let some (b, pf, aux) := kept then
                let t0 ← IO.monoMsNow
                if ← keptOk b pf aux then
                  cakeLog s!"[mutual] member {i} {members[i]!} kept (checked in {(← IO.monoMsNow) - t0}ms)"
                  addConstInfos aux
                  return (b, pf, ← newConstsSince env0 #[b, pf])
                cakeLog s!"[mutual] member {i} {members[i]!}: kept proof rejected, solving"
              let (b, pf) ← solveMember i p ih (collect := true)
              pure (b, pf, ← newConstsSince env0 #[b, pf])
          let act ← Core.wrapAsync (fun (_ : Unit) => job.run' mctx mst) none
          jobs.modify (·.push (i, ph.mvarId!, act))
          pure ph) s
        mkLambdaFVars #[s] pf
      let js ← jobs.get
      let nKept := (← reused.get).size
      let next ← IO.mkRef 0
      -- a worker keeps going after a failure, so that one round collects every
      -- unit and datatype the block still needs (and keeps every finished member)
      let worker : BaseIO (Array (Nat × Expr × Expr × Array ConstantInfo) × Bool) := do
        let mut out := #[]
        let mut failed := false
        repeat
          let k ← next.modifyGet fun k => (k, k + 1)
          if h : k < js.size then
            let (i, _, act) := js[k]
            match ← (act ()).toBaseIO with
            | .ok (b, pf, aux) => out := out.push (i, b, pf, aux)
            | .error _ => failed := true
          else break
        return (out, failed)
      needUnitsAllRef.set #[]
      needDatatypesAllRef.set #[]
      let t0 ← IO.monoMsNow
      cakeLog s!"[mutual] solving {js.size} members with {par} workers ({nKept} kept from the previous round)"
      let tasks ← (List.range (min par js.size)).toArray.mapM fun _ => BaseIO.asTask worker .dedicated
      let mut fresh : Array (Nat × Expr × Expr × Array ConstantInfo) := #[]
      let mut anyFailed := false
      for t in tasks do
        let (out, failed) ← IO.wait t
        fresh := fresh ++ out
        anyFailed := anyFailed || failed
      cakeLog s!"[mutual] parallel members done in {(← IO.monoMsNow) - t0}ms"
      -- requests first: a round that recorded any is discarded even if every
      -- member "succeeded" (its proofs then contain `sorry`); its complete
      -- members are kept for the retry
      let dedup (xs : Array Expr) : Array Expr := xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]
      let dts := dedup (← needDatatypesAllRef.get)
      let units := dedup (← needUnitsAllRef.get)
      if dts.size + units.size > 0 then
        let mut results := Array.replicate members.size (none : Option (Expr × Expr × Array ConstantInfo))
        for (i, b, pf, aux) in fresh do
          if !pf.hasSorry then results := results.set! i (some (b, pf, aux))
        let nKeep := results.foldl (fun n r => if r.isSome then n + 1 else n) 0
        mutualCacheRef.set (some { block := members, cnames := cnamesNow, unames := unamesNow, fixed, fixedTys, deps, depFVars := depHyps, depTys,
                                   pih := ← pihs.get, results })
        cakeLog s!"[mutual] parallel round needs {dts.size} datatypes, {units.size} units; {nKeep} members kept"
      if h : 0 < dts.size then
        -- the retry loop registers it and retries the block
        saved.restore
        needUnitRef.set none
        needDatatypeRef.set (some dts[0])
        throwError "cake: need datatype {dts[0]}"
      else if h : 0 < units.size then
        -- the retry loop translates all of them, then retries the block once
        saved.restore
        needDatatypeRef.set none
        needUnitRef.set (some units[0])
        pendingUnitsRef.set (units.extract 1 units.size)
        throwError "{needUnitTag}{units[0]}"
      if anyFailed then
        cakeLog s!"[mutual] a parallel member failed: rerunning sequentially"
        saved.restore
        sequentialStep
      else
        -- in member order, so that the environment does not depend on thread timing
        for (i, b, pf, aux) in fresh.qsort (·.1 < ·.1) do
          addConstInfos aux
          bodies[i]!.mvarId!.assign b
          let some (_, ph, _) := js.find? (·.1 == i) | throwError "lost member {i}"
          ph.assign pf
        let step ← instantiateMVars skel
        if step.hasExprMVar || step.hasSorry then
          cakeLog s!"[mutual] parallel step has unassigned metavariables or sorry: rerunning sequentially"
          saved.restore
          sequentialStep
        else pure step
    cakeLog s!"[mutual] induction step built"
    let joint ← withLocalDeclD `s S fun s => do
      mkLambdaFVars #[s] (← withTransparency .all <| mkAppOptM ``WellFounded.induction #[S, r, hwf, Pred, s, step])
    -- the joint theorem over all hypotheses
    let allHyps := #[envC, funs, hnodup] ++ hfinds ++ common ++ hselfs ++ has ++ depHyps
    let jointName := infos[0]!.2.2.2.1 ++ `joint
    let jointPf ← instantiateMVars (← mkLambdaFVars allHyps joint)
    let jointTy ← instantiateMVars (← inferType jointPf)
    cakeLog s!"[mutual] adding joint theorem"
    addDecl (Declaration.thmDecl (mkTheoremValEx jointName [] jointTy jointPf []))
    cakeLog s!"[mutual] joint theorem added"
    let jointApp := mkAppN (mkConst jointName) allHyps
    -- each member's certificate: the joint theorem at its injection
    let peerNames := infos.map (·.2.2.2.1)
    for i in [0:members.size] do
      let (n, τ, _, uname, cname) := infos[i]!
      let pf ← withLocalDeclD `t τ fun t => do mkLambdaFVars #[t] (mkApp jointApp (← sumInj taus i t))
      let peerHyps := ((List.range members.size).filter (· != i)).foldl (fun acc j => acc ++ #[hfinds[j]!, hselfs[j]!]) #[]
      let hyps := #[envC, funs, hnodup, hfinds[i]!] ++ common ++ #[hselfs[i]!] ++ has ++ peerHyps ++ depHyps
      let inv ← mkAppM ``Arrow #[invTs[i]!, invBs[i]!]
      let peers := peerNames.filter (· != uname)
      finishUnit keys[i]! uname cname (.function param (uname ++ `body) (n > 1)) deps bodies[i]! hyps envC funs pf
        fts[i]! inv peers

/-- Is `c` defined by recursion (structural or well-founded)? -/
def isRecursiveDef (c : Name) : MetaM Bool := do
  let env ← getEnv
  return (Lean.Elab.Structural.eqnInfoExt.find? env c).isSome || (Lean.Elab.WF.eqnInfoExt.find? env c).isSome

def translateUnitOnce (key : Expr) (extra : Array Expr) : MetaM Unit := do
  if (getUnit? (← getEnv) key).isSome then return
  let .const c _ := key.getAppFn | throwError "unit key {key} is not a constant application"
  let isFn : Bool ← forallTelescope (← inferType key) fun xs _ => pure (decide (xs.size > 0))
  let ms ← mutualMembers c
  if !ms.isEmpty then
    unless key.getAppArgs.isEmpty do throwError "mutual block with static arguments is not supported yet: {key}"
    return ← translateMutual ms extra
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

/-- Constants the solver translates natively (never units). -/
def nativeHeads : List Name :=
  [``Int.add, ``Int.sub, ``Int.mul, ``Int.neg, ``Int.ofNat, ``Int.negSucc, ``Int.decEq, ``Int.decLe, ``Int.decLt,
   ``Nat.add, ``Nat.mul, ``Nat.cast, ``Decidable.decide, ``ite, ``dite, ``cond, ``Decidable.isTrue,
   ``Decidable.isFalse, ``Eq.mpr, ``Eq.mp, ``Eq.ndrec, ``cast, ``Quot.mk, ``Quot.lift, ``id]

/-- Candidate unit keys mentioned by the unfolding equations of a mutual
block's members: applications of defined constants (not members, constructors,
recursors or matchers) to closed static arguments. -/
partial def blockCandidates (ms : Array Name) : MetaM (Array Expr) := do
  let env ← getEnv
  let found ← IO.mkRef (#[] : Array Expr)
  let seenInst ← IO.mkRef (#[] : Array Expr)
  let rec visit (e : Expr) : MetaM Unit := do
    match e with
    | .app .. | .const .. =>
      -- class methods at instances (e.g. `bind` of `StateT σ m`): what they unfold to
      if !e.hasLooseBVars then
        if let some e' ← (try Meta.unfoldProjInst? e catch _ => pure none) then
          let e' := e'.headBeta
          if !(← seenInst.get).contains e' then
            seenInst.modify (·.push e')
            visit e'
      if let .const c _ := e.getAppFn then
        -- a replaced constant is never translated itself (its replacement is)
        if !ms.contains c && !(isAuxRecursor env c) && !(← Meta.isMatcher c) && !nativeHeads.contains c &&
            !(replaceExt.getState env).contains c && !(rewriteExt.getState env).contains c then
          if let some (.defnInfo _) := env.find? c then
            if let some (k, _) ← splitKey e then
              if !k.hasFVar && !k.hasMVar && !(← found.get).contains k then
                -- functions and constants only: no types, propositions or instances
                let kty ← inferType k
                let isTy ← isTypeFormerType kty
                let isPr ← isProp kty
                let isInst ← isInstance c
                if !isTy && !isPr && !isInst then found.modify (·.push k)
      for a in e.getAppArgs do visit a
      unless e.getAppFn.isConst do visit e.getAppFn
    | .lam _ ty b _ | .forallE _ ty b _ =>
      visit ty; withLocalDeclD `x ty fun x => visit (b.instantiate1 x)
    | .letE _ ty v b _ =>
      visit ty; visit v; withLocalDeclD `x ty fun x => visit (b.instantiate1 x)
    | .mdata _ e' => visit e'
    | .proj _ _ e' => visit e'
    | _ => pure ()
  for c in ms do
    if let some eqn ← getUnfoldEqnFor? c (nonRec := true) then
      forallTelescope (← inferType (mkConst eqn)) fun _ ty => do
        if let some (_, _, rhs) := ty.eq? then visit rhs
  -- cached computed fields: a constructor application translates the field's
  -- definition at that constructor, so what it calls is needed too
  -- (and the solver unfolds the non-recursive helpers it calls, e.g. `mkAppData`
  -- into `packData`/`hash32`: follow those a few levels)
  let before := (← found.get).size
  for (_, fs) in (cachedExt.getState env).toList do
    for f in fs do
      if let some v := (env.find? f).bind (·.value?) then visit v
  let mut frontier := (← found.get).extract before (← found.get).size
  for _ in [0:3] do
    let start := (← found.get).size
    for k in frontier do
      if let .const c _ := k.getAppFn then
        if !(← isRecursiveDef c) then
          if let some v := (env.find? c).bind (·.value?) then visit v
    frontier := (← found.get).extract start (← found.get).size
  found.get

mutual
/-- The dependency pre-pass of `key`'s mutual block: translate (best effort) the
constants the members' equations mention; returns the candidates. -/
partial def prepassBlock (key : Expr) (stack : List Expr := []) : MetaM (Array Expr) := do
  let .const c _ := key.getAppFn | return #[]
  let ms ← mutualMembers c
  if ms.isEmpty then return #[]
  let t0 ← IO.monoMsNow
  let cands ← blockCandidates ms
  cakeLog s!"[prepass] {c}: {cands.size} candidates in {(← IO.monoMsNow) - t0}ms"
  for k in cands do
    if (getUnit? (← getEnv) k).isNone && !stack.contains k && !(ms.contains k.getAppFn.constName!) then
      cakeLog s!"[prepass] {c}: candidate {((← ppExpr k).pretty.replace "\n" " ").take 120}"
      let s0 ← saveState
      try translateUnit k (key :: stack)
      catch e =>
        let msg ← e.toMessageData.toString
        if (msg.splitOn "cake: need datatype").length > 1 then throw e
        -- keep the units (and datatypes) completed on the way: they are sound
        let env ← getEnv
        s0.restore
        setEnv env
        cakeLog s!"[prepass] {c}: candidate failed: {msg.take 300}"
  cakeLog s!"[prepass] {c}: done"
  return cands

/-- Translate `key`, first translating (recursively) the units it needs.
Units needed only after unfolding (not visible in the body) are added to the
dependencies explicitly (`extra`). -/
partial def translateUnit (key : Expr) (stack : List Expr := []) (extra : Array Expr := #[]) :
    MetaM Unit := do
  if (getUnit? (← getEnv) key).isSome then return
  if stack.contains key then throwError "cyclic unit dependency at {key} (mutual recursion is not supported yet)"
  if stack.length > 200 then throwError "unit dependency chain too deep at {key}"
  -- a mutual block: translate the constants its members' equations mention first
  -- (best effort), so the block is not restarted for every dependency it discovers
  let mut extra := extra
  if extra.isEmpty && (← IO.getEnv "CAKE_NOPREPASS").isNone then
    if let .const c _ := key.getAppFn then
      let ms ← mutualMembers c
      if !ms.isEmpty then
        let cands ← prepassBlock key stack
        -- every candidate that is a unit is a dependency up front (also those only
        -- reached after unfolding, which the block's equations do not mention)
        let envNow ← getEnv
        extra := cands.filter fun k => (getUnit? envNow k).isSome
  -- a split block: the extra dependencies recorded by `cake_mutual_prepare`
  if let (some (t, _), .const c _) := (← mutualSplitRef.get, key.getAppFn) then
    if c == t then
      for d in ((splitExtraExt.getState (← getEnv)).find? t).getD #[] do
        unless extra.contains d do extra := extra.push d

  let saved ← saveState
  needUnitRef.set none
  pendingUnitsRef.set #[]
  -- collect every missing unit of this attempt (their goals are closed by `sorry`,
  -- and the attempt is discarded): one retry instead of one per missing unit.
  -- An enclosing attempt's state is kept aside and restored on every exit.
  let outerCollect ← collectAllRef.get
  let outerNeeds ← needUnitsAllRef.get
  collectAllRef.set (← IO.getEnv "CAKE_NOCOLLECT").isNone
  needUnitsAllRef.set #[]
  let dedup (xs : Array Expr) : Array Expr := xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]
  let restoreOuter : MetaM Unit := do
    collectAllRef.set outerCollect
    needUnitsAllRef.set outerNeeds
  try
    let t0 ← IO.monoMsNow
    let nm := (← ppExpr key).pretty.take 120
    cakeLog s!"[cake] start unit {nm}"
    withCurrHeartbeats (translateUnitOnce key extra)
    let ns := dedup (← needUnitsAllRef.get)
    if h : 0 < ns.size then
      cakeLog s!"[cake] unit {nm} needs {ns.size} units"
      needUnitRef.set (some ns[0])
      pendingUnitsRef.set (ns.extract 1 ns.size)
      throwError "{needUnitTag}{ns[0]}"
    restoreOuter
    cakeLog s!"[cake] {(← IO.monoMsNow) - t0}ms unit {nm}"
  catch e =>
    -- all the units this attempt asked for (also when it failed otherwise, e.g.
    -- on a goal shaped by a `sorry`)
    let collected := dedup ((← needUnitRef.get).toArray ++ (← pendingUnitsRef.get) ++ (← needUnitsAllRef.get))
    restoreOuter
    if (← IO.getEnv "CAKE_DEBUG_COLLECT").isSome then
      cakeLog s!"[collect-debug] attempt ended with {collected.size} collected: {((← e.toMessageData.toString).replace "\n" " ").take 300}"
    if h : 0 < collected.size then
      needUnitRef.set (some collected[0])
      pendingUnitsRef.set (collected.extract 1 collected.size)
    -- a missing datatype: register it in place and retry this unit only
    if let some τ ← needDatatypeRef.get then
     if (← IO.getEnv "CAKE_NOHOOK").isNone then
      saved.restore
      needDatatypeRef.set none
      (← datatypeHookRef.get) τ
      return ← translateUnit key stack extra
    match ← needUnitRef.get with
    | some dep =>
      saved.restore
      needUnitRef.set none
      let pending ← pendingUnitsRef.get
      pendingUnitsRef.set #[]
      if extra.contains dep then
        throwError "while translating {key}: unit {dep} is in scope but still needed: {e.toMessageData}"
      translateUnit dep (key :: stack)
      let mut extra' := extra.push dep
      -- the other units a parallel round asked for, all before the one retry
      for d in pending do
        unless extra'.contains d do
          translateUnit d (key :: stack)
          extra' := extra'.push d
      translateUnit key stack extra'
    | none =>
      saved.restore
      throwError "while translating {key}: {e.toMessageData}"
end

end ConPastel.Translator.Meta
