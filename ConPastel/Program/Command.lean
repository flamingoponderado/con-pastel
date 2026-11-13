import ConPastel.Program.Assemble
import ConPastel.Translator.Meta.Unit

/-!
# `cake_program`: assemble the translated units into a program

`cake_program P entry` builds, from every registered unit:
* `P.funs`, the single recursive group (one entry per unit);
* `P.cert_k`, unit `%k`'s certificate instantiated at `initEnv` and `P.funs`,
  in registration order (a unit's dependencies are registered before it);
* `P.prog`, the program, and `P.correct`: for every input, `P.prog`
  completes, writing `entry`'s verdict on the input bytes.

The program declares every registered datatype in one `Dtype` (stamps from 2,
in registration order), then the group, then the main program.
-/

namespace ConPastel.Program
open Lean Meta Elab Command ConPastel.Translator.Meta
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

def unitsInOrder (env : Environment) : Array UnitInfo :=
  let key (u : UnitInfo) : Nat := (u.cname.drop 1).toNat!
  (allUnits env).qsort (fun a b => key a < key b)

def addThm (n : Name) (pf : Expr) : MetaM Unit := do
  let pf ← instantiateMVars pf
  addDecl (Declaration.thmDecl (mkTheoremValEx n [] (← inferType pf) pf []))

def addDef (n : Name) (ty val : Expr) : MetaM Unit :=
  addDecl (Declaration.defnDecl (mkDefinitionValEx n [] ty val .abbrev .safe []))

def cakeProgram (P entry : Name) : MetaM Unit := do
  let env ← getEnv
  let us := unitsInOrder env
  let some eu := us.find? (·.key == mkConst entry) | throwError "{entry} is not a unit"
  let some ru := us.find? (·.key == mkConst ``ConPastel.Main.revApp) | throwError "revApp is not a unit"
  -- the datatypes, in stamp order
  let dts := allDatatypes env
  let astT := mkConst ``AstT
  let tyVar ← mkAppM ``AstT.atvar #[mlString "'a"]
  let tdTy ← mkAppM ``Prod #[← mkAppM ``List #[mkConst ``TvarN], ← mkAppM ``Prod #[mkConst ``TypeN,
    ← mkAppM ``List #[← mkAppM ``Prod #[mkConst ``ConN, ← mkAppM ``List #[astT]]]]]
  let tdEntries ← dts.toList.mapM fun d => do
    let ctors ← d.ctors.toList.mapM fun (_, cn, flags) => do
      mkAppM ``Prod.mk #[mlString cn, ← mkListLit astT (List.replicate (flags.toList.filter id).length tyVar)]
    let ctorTy ← mkAppM ``Prod #[mkConst ``ConN, ← mkAppM ``List #[astT]]
    mkAppM ``Prod.mk #[← mkListLit (mkConst ``TvarN) [], ← mkAppM ``Prod.mk #[mlString d.name.toString,
      ← mkListLit ctorTy ctors]]
  addDef (P ++ `tds) (mkConst ``TypeDef) (← mkListLit tdTy tdEntries)
  let tds := mkConst (P ++ `tds)
  let envC ← mkAppM ``dtEnv #[tds]
  let envCc ← mkAppM ``SemEnv.c #[envC]
  let hdup ← closeWith (← mkEq (← mkAppM ``List.all #[tds, mkConst ``checkDupCtors]) (mkConst ``Bool.true))
    (← `(tactic| decide))
  let hbool ← closeWith (← mkAppM ``ConPastel.Translator.HasBoolCons #[envCc])
    (← `(tactic| exact ⟨by decide, by decide⟩))
  let hlist ← closeWith (← mkAppM ``ConPastel.Translator.HasListCons #[envCc])
    (← `(tactic| exact ⟨by decide, by decide⟩))
  -- the group
  let fty ← funTy
  let entries ← us.toList.mapM fun u => do
    let (param, body) := match u.kind with
      | .function p b _ => (p, b)
      | .thunk p b => (p, b)
    mkAppM ``Prod.mk #[mlString u.cname, ← mkAppM ``Prod.mk #[mlString param, mkConst body]]
  addDef (P ++ `funs) (← mkAppM ``List #[fty]) (← mkListLit fty entries)
  let funs := mkConst (P ++ `funs)
  let nodupTy ← mkAppM ``List.Nodup #[← mkAppM ``List.map #[← withLocalDeclD `p fty fun p => do
    mkLambdaFVars #[p] (← mkAppM ``Prod.fst #[p]), funs]]
  addThm (P ++ `nodup) (← closeWith nodupTy (← `(tactic| decide)))
  let nodup := mkConst (P ++ `nodup)
  -- certificates, in registration order, all under `h : RuntimeAssumptions`
  withLocalDeclD `h (mkConst ``ConPastel.RuntimeAssumptions) fun hrt => do
  let mut certs : Std.HashMap Expr Expr := {}
  let mut lookups : Std.HashMap Expr Expr := {}
  for u in us do
    let tag := u.cname.drop 1
    let lk ← closeWith (← groupLookupTy envC funs u.cname)
      (← `(tactic| exact ConPastel.Translator.nsLookup_buildRecEnv (by decide)))
    addThm (P ++ Name.mkSimple s!"lookup_{tag}") lk
    let lkC := mkConst (P ++ Name.mkSimple s!"lookup_{tag}")
    lookups := lookups.insert u.key lkC
    let (param, body) := match u.kind with
      | .function p b _ => (p, b)
      | .thunk p b => (p, b)
    let findTy ← mkEq (← mkAppM ``findRecFun #[mlString u.cname, funs])
      (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[mlString param, mkConst body]])
    let hfind ← closeWith findTy (← `(tactic| rfl))
    let hcs ← u.datatypes.mapM fun T => do
      let nm := mkIdent (T ++ `cakeHasCons)
      closeWith (mkApp (mkConst (T ++ `cakeHasCons)) envCc) (← `(tactic| (unfold $nm:ident; decide)))
    let has ← u.assumes.mapM fun a => do
      let i1 := mkIdent `h.numBits
      let i2 := mkIdent `h.mixHash
      let i3 := mkIdent `h.stringHash
      closeWith a (← `(tactic| first | exact $i1:ident | exact $i2:ident | exact $i3:ident))
    let mut args : Array Expr := #[envC, funs, nodup, hfind, hbool, hlist] ++ hcs ++ #[lkC] ++ has
    for d in u.deps do
      let some dl := lookups.get? d | throwError "dependency {d} of {u.key} not assembled"
      let some dc := certs.get? d | throwError "dependency {d} of {u.key} not assembled"
      args := args ++ #[dl, dc]
    addThm (P ++ Name.mkSimple s!"cert_{tag}") (← mkLambdaFVars #[hrt] (mkAppN (mkConst u.cert) args))
    certs := certs.insert u.key (mkApp (mkConst (P ++ Name.mkSimple s!"cert_{tag}")) hrt)
  -- the program and its correctness
  let mainDecs ← mkAppM ``ConPastel.Main.mainDecs #[toExpr eu.cname, toExpr ru.cname]
  let loc := mkConst ``Flapjack.Misc.Location.unknownLoc
  let prog ← mkAppM ``List.cons #[← mkAppM ``Dec.dtype #[loc, tds],
    ← mkAppM ``List.cons #[← mkAppM ``Dec.dletrec #[loc, funs], mainDecs]]
  addDef (P ++ `prog) (← mkAppM ``List #[mkConst ``Dec]) prog
  -- constructor arities
  let cRed ← withTransparency .all <| reduce envCc (explicitOnly := false) (skipTypes := false)
  let (``Namespace.bind, #[_, _, _, l, _]) := cRed.getAppFnArgs
    | throwError "constructor environment did not reduce to a flat namespace: {cRed}"
  let hc ← closeWith (← mkEq envCc (← mkAppM ``Namespace.bind #[l, ← mkListLit (← mkAppM ``Prod
      #[mkConst ``ModN, ← mkAppM ``Namespace #[mkConst ``ModN, mkConst ``ConN,
        ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Stamp]]]) []]))
    (← `(tactic| rfl))
  let elemTy := (← inferType l).appArg!
  let tbl ← mkAppM ``List.map #[← withLocalDeclD `e elemTy fun e => do
      mkLambdaFVars #[e] (← mkAppM ``Prod.mk #[← mkAppM ``Prod.fst #[e], ← mkAppM ``Prod.fst #[← mkAppM ``Prod.snd #[e]]]), l]
  let conOkTy ← mkEq (← mkAppM ``conOkFuns #[tbl, funs]) (mkConst ``Bool.true)
  let hcon ← mkAppM ``group_conOk_of #[envC, l, hc, funs, ← closeWith conOkTy (← `(tactic| decide))]
  let memTy (n : String) : MetaM Expr := do
    mkAppM ``Membership.mem #[← mkAppM ``List.map #[← withLocalDeclD `p fty fun p => do
      mkLambdaFVars #[p] (← mkAppM ``Prod.fst #[p]), funs], mlString n]
  let hmemE ← closeWith (← memTy eu.cname) (← `(tactic| decide))
  let hmemR ← closeWith (← memTy ru.cname) (← `(tactic| decide))
  let ne (a b : String) : MetaM Expr := do closeWith (mkNot (← mkEq (mlString a) (mlString b))) (← `(tactic| decide))
  let some ce := certs.get? eu.key | unreachable!
  let some cr := certs.get? ru.key | unreachable!
  let pf ← mkAppOptM ``program_completes_dt #[tds, funs, toExpr eu.cname, toExpr ru.cname, mkConst entry, hdup,
    nodup, hcon, hmemE, hmemR, ce, cr, hlist, ← ne eu.cname ConPastel.Main.bufName,
    ← ne eu.cname ConPastel.Main.readAllName, ← ne ru.cname ConPastel.Main.bufName,
    ← ne ru.cname ConPastel.Main.readAllName]
  addThm (P ++ `correct) (← mkLambdaFVars #[hrt] pf)

elab "cake_program " P:ident entry:ident : command => do
  let e ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo entry
  liftTermElabM <| cakeProgram P.getId e

end ConPastel.Program
