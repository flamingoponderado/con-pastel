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
