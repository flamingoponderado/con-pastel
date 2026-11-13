import ConPastel.Translator.Meta.Goal
import ConPastel.Translator.Meta.Command
import ConPastel.Translator.Meta.Datatype

/-! # `cake_rec`: translate a recursive single-argument function -/

namespace ConPastel.Translator.Meta
open Lean Meta Elab Command
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

def translateRec1 (c : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let .forallE xn xty bty _ := ci.type | throwError "{c} is not a function"
  if bty.hasLooseBVars then throwError "dependent result type"
  let invA ← invOf xty
  let invB ← invOf bty
  let fname := c.toString
  let pname := "x"
  let some eqn ← getUnfoldEqnFor? c (nonRec := true) | throwError "no unfold equation for {c}"
  withLocalDeclD `envC (mkApp (mkConst ``SemEnv) (mkConst ``Value)) fun envC => do
  withLocalDeclD `hbool (← mkAppM ``HasBoolCons #[← mkAppM ``SemEnv.c #[envC]]) fun hbool => do
    let dts := (datatypeExt.getState (← getEnv)).toList.map (·.1)
    let envCc ← mkAppM ``SemEnv.c #[envC]
    withLocalDeclsDND (dts.toArray.map fun T => (`hc, mkApp (mkConst (T ++ `cakeHasCons)) envCc)) fun hcs => do
    let hasCons : NameMap Expr := (dts.zip hcs.toList).foldl (fun m (T, h) => m.insert T h) {}
    let body ← mkFreshExprMVar (mkConst ``Exp)
    let funTy ← mkAppM ``Prod #[mkConst ``VarN, ← mkAppM ``Prod #[mkConst ``VarN, mkConst ``Exp]]
    let funs ← mkListLit funTy [← mkAppM ``Prod.mk #[mlString fname, ← mkAppM ``Prod.mk #[mlString pname, body]]]
    let cl ← mkAppM ``Value.recclosure #[envC, funs, mlString fname]
    -- r := InvImage (· < ·) sizeOf
    let wfr ← mkAppOptM ``measure #[xty, ← mkAppOptM ``SizeOf.sizeOf #[xty, none]]
    let r ← mkAppOptM ``WellFoundedRelation.rel #[xty, wfr]
    let hwf ← mkAppOptM ``WellFoundedRelation.wf #[xty, wfr]
    let f := mkConst c
    let funTyI := funTy
    let nodupTy ← mkAppM ``List.Nodup #[← mkAppM ``List.map #[← withLocalDeclD `p funTyI fun p => do
      mkLambdaFVars #[p] (← mkAppM ``Prod.fst #[p]), funs]]
    let hnodup ← mkFreshExprMVar nodupTy
    let findTy ← mkEq (← mkAppM ``findRecFun #[mlString fname, funs])
      (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[mlString pname, body]])
    let hfind ← mkFreshExprMVar findTy
    let pfH ← withLocalDeclD xn xty fun x => do
      let ihTy ← withLocalDeclD `y xty fun y => do
        mkForallFVars #[y] (← mkArrow (mkApp2 r y x) (← withLocalDeclD `yv (mkConst ``Value) fun yv => do
          mkForallFVars #[yv] (← mkArrow (mkApp2 invA y yv) (← mkAppM ``AppReturns #[cl, yv, mkApp invB (mkApp f y)]))))
      withLocalDeclD `ih ihTy fun ih => do
      withLocalDeclD `xv (mkConst ``Value) fun xv => do
      withLocalDeclD `hx (mkApp2 invA x xv) fun hx => do
        let env ← mkAppM ``recBodyEnv #[envC, funs, mlString pname, xv]
        let g ← mkFreshExprMVar (← mkAppM ``Eval #[env, body, mkApp invB (mkApp f x)])
        let eqPf ← mkAppM eqn #[x]
        let rhs := (← inferType eqPf).appArg!
        let motive ← withLocalDeclD `t bty fun tt => do mkLambdaFVars #[tt] (← mkAppM ``Eval #[env, body, mkApp invB tt])
        let g' ← g.mvarId!.replaceTargetEq (mkApp motive rhs).headBeta (← mkCongrArg motive eqPf)
        let gctx : GCtx := { hbool, hasCons, rec? := some { head := c, static := #[], ih, cl, cname := fname } }
        let gst : GSt := { locals := #[{ fvar := x, cname := pname, value := xv, rel := hx }] }
        let _ ← (solve g').run gst |>.run gctx
        let app ← mkAppOptM ``AppReturns_recclosure #[envC, funs, mlString fname, mlString pname, body, xv,
          mkApp invB (mkApp f x), hnodup, hfind, g]
        mkLambdaFVars #[x, ih, xv, hx] app
    -- side conditions, now that the body is known
    hnodup.mvarId!.assign (← closeWith (← instantiateMVars nodupTy) (← `(tactic| decide)))
    hfind.mvarId!.assign (← closeWith (← instantiateMVars findTy) (← `(tactic| simp [findRecFun])))
    let pf ← mkAppOptM ``arrow_of_wf #[xty, bty, invA, invB, r, hwf, f, cl, pfH]
    let pf ← instantiateMVars pf
    let bodyI ← instantiateMVars body
    let bodyName := c ++ `cake_body
    addDecl (Declaration.defnDecl (mkDefinitionValEx bodyName [] (mkConst ``Exp) bodyI .abbrev .safe []))
    -- statement over the named body
    let funsN ← mkListLit funTy [← mkAppM ``Prod.mk #[mlString fname, ← mkAppM ``Prod.mk #[mlString pname, mkConst bodyName]]]
    let clN ← mkAppM ``Value.recclosure #[envC, funsN, mlString fname]
    let stmt ← mkForallFVars (#[envC, hbool] ++ hcs) (mkApp2 (← mkAppM ``Arrow #[invA, invB]) f clN)
    let pf ← mkLambdaFVars (#[envC, hbool] ++ hcs) pf
    unless ← isDefEq (← inferType pf) stmt do
      throwError "certificate type mismatch"
    addDecl (Declaration.thmDecl (mkTheoremValEx (c ++ `cake_cert) [] stmt pf []))

elab "cake_rec " id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM <| translateRec1 c

end ConPastel.Translator.Meta

namespace ConPastel.Translator.Meta
open Lean Meta Elab Command
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- Right-nested tuple type of `tys`. -/
def tupleTy (tys : List Expr) : MetaM Expr :=
  match tys with
  | [] => throwError "empty tuple"
  | [t] => pure t
  | t :: ts => do mkAppM ``Prod #[t, ← tupleTy ts]

/-- Projections of a right-nested tuple `p` with `m` components. -/
partial def tupleProjs (p : Expr) (m : Nat) : MetaM (List Expr) := do
  if m ≤ 1 then return [p]
  return (← mkAppM ``Prod.fst #[p]) :: (← tupleProjs (← mkAppM ``Prod.snd #[p]) (m - 1))

/-- The structural recursion argument of `c`, if Lean recorded one. -/
def structRecArg? (c : Name) : MetaM (Option Nat) := do
  let env ← getEnv
  match Lean.Elab.Structural.eqnInfoExt.find? env c with
  | some info => return some info.recArgPos
  | none => return none

/-- Destructure the tuple local `p` (with `m` components) into locals, then
solve the goal for `f a₁ … aₙ`, unfolded. -/
partial def destructAndSolve (g : MVarId) (env invB : Expr) (f : Expr) (eqn : Name)
    (pre : Array Expr) (p : Expr) (m : Nat) : GoalM Unit := do
  if m == 1 then
    let as := pre.push p
    let t := mkAppN f as
    let eqPf ← mkAppM eqn as
    let rhs := (← inferType eqPf).appArg!
    let ce ← evalGoalCe g
    let motive ← withLocalDeclD `t (← inferType t) fun tt => do
      mkLambdaFVars #[tt] (← mkAppM ``Eval #[env, ce, mkApp invB tt])
    let g' ← g.replaceTargetEq (mkApp motive rhs).headBeta (← mkCongrArg motive eqPf)
    return ← solve g'
  let st ← get
  let some lv := st.locals.find? (·.fvar == p) | throwError "tuple local not found"
  let pty ← whnfR (← inferType p)
  let (``Prod, #[aty, bty]) := pty.getAppFnArgs | throwError "tuple expected"
  let invP ← invOf pty
  let (``PAIR, #[_, _, invA, invRest]) := invP.getAppFnArgs | throwError "PAIR expected"
  let xn ← freshCName "t"
  let yn ← freshCName "t"
  let hl ← proveLookupG env lv.cname lv.value
  let he ← mkAppOptM ``Eval_var #[env, shortIdent lv.cname, lv.value, mkApp invP p, hl, lv.rel]
  -- continuation g a b := f pre a (projs b)
  let gfun ← withLocalDeclD `a aty fun a => withLocalDeclD `b bty fun b => do
    mkLambdaFVars #[a, b] (mkAppN f (pre.push a ++ (← tupleProjs b (m - 1)).toArray))
  let hxy ← closeWith (mkNot (← mkEq (mlString xn) (mlString yn))) (← `(tactic| decide))
  let body ← mkFreshExprMVar (mkConst ``Exp)
  let hb ← withLocalDeclD `a aty fun a => withLocalDeclD `b bty fun b => do
    withLocalDeclD `heq (← mkEq p (← mkAppM ``Prod.mk #[a, b])) fun heq => do
    withLocalDeclD `av (mkConst ``Value) fun av => withLocalDeclD `bv (mkConst ``Value) fun bv => do
    withLocalDeclD `hav (mkApp2 invA a av) fun hav => withLocalDeclD `hbv (mkApp2 invRest b bv) fun hbv => do
      let env' ← mkAppM ``clauseEnv #[env, ← mkListLit (mkConst ``VarN) [mlString xn, mlString yn],
        ← mkListLit (mkConst ``Value) [av, bv]]
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env', body, mkApp invB (gfun.beta #[a, b])])
      let saved := (← get).locals
      let la : GLVar := { fvar := a, cname := xn, value := av, rel := hav }
      let lb : GLVar := { fvar := b, cname := yn, value := bv, rel := hbv }
      modify fun s => { s with locals := s.locals.push la |>.push lb }
      destructAndSolve gb.mvarId! env' invB f eqn (pre.push a) b (m - 1)
      modify fun s => { s with locals := saved }
      mkLambdaFVars #[a, b, heq, av, bv, hav, hbv] (← instantiateMVars gb)
  let pf ← mkAppOptM ``Eval_mat_pair #[aty, bty, none, invA, invRest, invB, env, none, body,
    mlString xn, mlString yn, p, gfun, hxy, he, hb]
  -- the goal is `invB (f pre p…)`, defeq to `invB (gfun p.1 p.2)`
  assignProof g pf

def translateRecTupled (c : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs resTy => do
  let n := xs.size
  let tys ← xs.mapM inferType
  let τ ← tupleTy tys.toList
  let invT ← invOf τ
  let invB ← invOf resTy
  let f := mkConst c
  -- the tupled function as a definition
  let tupName := c ++ `cake_tupled
  let tupVal ← withLocalDeclD `p τ fun p => do mkLambdaFVars #[p] (mkAppN f (← tupleProjs p n).toArray)
  addDecl (Declaration.defnDecl (mkDefinitionValEx tupName [] (← mkArrow τ resTy) tupVal .abbrev .safe []))
  let ft := mkConst tupName
  let some recArg ← structRecArg? c | throwError "{c}: only structural recursion is supported for now"
  let some eqn ← getUnfoldEqnFor? c (nonRec := true) | throwError "no unfold equation for {c}"
  let fname := tupName.toString
  let pname := "p"
  withLocalDeclD `envC (mkApp (mkConst ``SemEnv) (mkConst ``Value)) fun envC => do
  withLocalDeclD `hbool (← mkAppM ``HasBoolCons #[← mkAppM ``SemEnv.c #[envC]]) fun hbool => do
    let dts := (datatypeExt.getState (← getEnv)).toList.map (·.1)
    let envCc ← mkAppM ``SemEnv.c #[envC]
    withLocalDeclsDND (dts.toArray.map fun T => (`hc, mkApp (mkConst (T ++ `cakeHasCons)) envCc)) fun hcs => do
    let hasCons : NameMap Expr := (dts.zip hcs.toList).foldl (fun m (T, h) => m.insert T h) {}
    let body ← mkFreshExprMVar (mkConst ``Exp)
    let funTy ← mkAppM ``Prod #[mkConst ``VarN, ← mkAppM ``Prod #[mkConst ``VarN, mkConst ``Exp]]
    let funs ← mkListLit funTy [← mkAppM ``Prod.mk #[mlString fname, ← mkAppM ``Prod.mk #[mlString pname, body]]]
    let cl ← mkAppM ``Value.recclosure #[envC, funs, mlString fname]
    -- measure: sizeOf of the structural argument
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
        let gctx : GCtx := { hbool, hasCons, rec? := some { head := c, static := #[], ih, cl, cname := fname, arity := n } }
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
    let stmt ← mkForallFVars (#[envC, hbool] ++ hcs) (mkApp2 (← mkAppM ``Arrow #[invT, invB]) ft clN)
    let pf ← mkLambdaFVars (#[envC, hbool] ++ hcs) pf
    unless ← isDefEq (← inferType pf) stmt do throwError "certificate type mismatch"
    addDecl (Declaration.thmDecl (mkTheoremValEx (c ++ `cake_cert) [] stmt pf []))

elab "cake_recn " id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM <| translateRecTupled c

end ConPastel.Translator.Meta
