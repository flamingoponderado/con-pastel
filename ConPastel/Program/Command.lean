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

Datatypes are not supported here yet: the group's environment is `initEnv`.
-/

namespace ConPastel.Program
open Lean Meta Elab Command ConPastel.Translator.Meta
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

def unitsInOrder (env : Environment) : Array UnitInfo :=
  let us := (unitExt.getState env).toList.map (·.2)
  let key (u : UnitInfo) : Nat := (u.cname.drop 1).toNat!
  us.toArray.qsort (fun a b => key a < key b)

def addThm (n : Name) (pf : Expr) : MetaM Unit := do
  let pf ← instantiateMVars pf
  addDecl (Declaration.thmDecl (mkTheoremValEx n [] (← inferType pf) pf []))

def addDef (n : Name) (ty val : Expr) : MetaM Unit :=
  addDecl (Declaration.defnDecl (mkDefinitionValEx n [] ty val .abbrev .safe []))

def cakeProgram (P entry : Name) : MetaM Unit := do
  let env ← getEnv
  unless (datatypeExt.getState env).isEmpty do throwError "cake_program: datatypes not supported yet"
  let us := unitsInOrder env
  let some eu := us.find? (·.const == entry) | throwError "{entry} is not a unit"
  let some ru := us.find? (·.const == ``ConPastel.Main.revApp) | throwError "revApp is not a unit"
  -- the group
  let fty ← funTy
  let entries ← us.toList.mapM fun u => do
    let (param, body) := match u.kind with
      | .function p b _ => (p, b)
      | .thunk p b => (p, b)
    mkAppM ``Prod.mk #[mlString u.cname, ← mkAppM ``Prod.mk #[mlString param, mkConst body]]
  addDef (P ++ `funs) (← mkAppM ``List #[fty]) (← mkListLit fty entries)
  let funs := mkConst (P ++ `funs)
  let envC := mkConst ``ConPastel.initEnv
  let nodupTy ← mkAppM ``List.Nodup #[← mkAppM ``List.map #[← withLocalDeclD `p fty fun p => do
    mkLambdaFVars #[p] (← mkAppM ``Prod.fst #[p]), funs]]
  addThm (P ++ `nodup) (← closeWith nodupTy (← `(tactic| decide)))
  let nodup := mkConst (P ++ `nodup)
  -- certificates, in registration order
  let mut certs : NameMap Expr := {}
  let mut lookups : NameMap Expr := {}
  for u in us do
    let tag := u.cname.drop 1
    let lk ← closeWith (← groupLookupTy envC funs u.cname)
      (← `(tactic| exact ConPastel.Translator.nsLookup_buildRecEnv (by decide)))
    addThm (P ++ Name.mkSimple s!"lookup_{tag}") lk
    let lkC := mkConst (P ++ Name.mkSimple s!"lookup_{tag}")
    lookups := lookups.insert u.const lkC
    let (param, body) := match u.kind with
      | .function p b _ => (p, b)
      | .thunk p b => (p, b)
    let findTy ← mkEq (← mkAppM ``findRecFun #[mlString u.cname, funs])
      (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[mlString param, mkConst body]])
    let hfind ← closeWith findTy (← `(tactic| rfl))
    let mut args : Array Expr := #[envC, funs, nodup, hfind,
      mkConst ``ConPastel.Translator.initEnv_hasBoolCons, mkConst ``ConPastel.Translator.initEnv_hasListCons, lkC]
    for d in u.deps do
      let some dl := lookups.find? d | throwError "dependency {d} of {u.const} not assembled"
      let some dc := certs.find? d | throwError "dependency {d} of {u.const} not assembled"
      args := args ++ #[dl, dc]
    addThm (P ++ Name.mkSimple s!"cert_{tag}") (mkAppN (mkConst u.cert) args)
    certs := certs.insert u.const (mkConst (P ++ Name.mkSimple s!"cert_{tag}"))
  -- the program and its correctness
  let mainDecs ← mkAppM ``ConPastel.Main.mainDecs #[toExpr eu.cname, toExpr ru.cname]
  let prog ← mkAppM ``List.cons #[← mkAppM ``Dec.dletrec #[mkConst ``Flapjack.Misc.Location.unknownLoc, funs], mainDecs]
  addDef (P ++ `prog) (← mkAppM ``List #[mkConst ``Dec]) prog
  let conOkTy ← mkEq (← mkAppM ``conOkFuns #[mkConst ``initTable, funs]) (mkConst ``Bool.true)
  let hcon ← mkAppM ``group_conOk #[funs, ← closeWith conOkTy (← `(tactic| decide))]
  let memTy (n : String) : MetaM Expr := do
    mkAppM ``Membership.mem #[← mkAppM ``List.map #[← withLocalDeclD `p fty fun p => do
      mkLambdaFVars #[p] (← mkAppM ``Prod.fst #[p]), funs], mlString n]
  let hmemE ← closeWith (← memTy eu.cname) (← `(tactic| decide))
  let hmemR ← closeWith (← memTy ru.cname) (← `(tactic| decide))
  let ne (a b : String) : MetaM Expr := do closeWith (mkNot (← mkEq (mlString a) (mlString b))) (← `(tactic| decide))
  let some ce := certs.find? eu.const | unreachable!
  let some cr := certs.find? ru.const | unreachable!
  let pf ← mkAppOptM ``program_completes #[funs, toExpr eu.cname, toExpr ru.cname, mkConst entry, nodup, hcon,
    hmemE, hmemR, ce, cr, ← ne eu.cname ConPastel.Main.bufName, ← ne eu.cname ConPastel.Main.readAllName,
    ← ne ru.cname ConPastel.Main.bufName, ← ne ru.cname ConPastel.Main.readAllName]
  addThm (P ++ `correct) pf

elab "cake_program " P:ident entry:ident : command => do
  let e ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo entry
  liftTermElabM <| cakeProgram P.getId e

end ConPastel.Program
