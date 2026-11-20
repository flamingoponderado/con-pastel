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

A primitive's body builds no constructor values of registered datatypes, so
its certificate takes no `cakeHasCons` hypotheses; it may be registered after
datatypes (e.g. CakeML's `=` on one, `ConPastel.Leche.Sharing`).
-/

namespace ConPastel.Translator.Meta
open Lean Meta Elab Command Term
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

def primitiveStatement (key body : Expr) (cname : String) (assumes : Array Expr := #[]) : MetaM Expr := do
  let isFn : Bool ← forallTelescope (← inferType key) fun xs _ => pure (decide (xs.size > 0))
  let (inv, target) ← if isFn then pure (← invOf (← inferType key), key) else do
    let t ← withLocalDeclD `u (mkConst ``Unit) fun x => mkLambdaFVars #[x] key
    pure (← mkAppM ``Arrow #[mkConst ``UNIT, ← invOf (← inferType key)], t)
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
  withLocalDeclsDND (assumes.map fun a => (`ha, a)) fun has => do
    let cl ← mkAppM ``Value.recclosure #[envC, funs, mlString cname]
    mkForallFVars (#[envC, funs, hnodup, hfind, hbool, hlist, hself] ++ has) (mkApp2 inv target cl)

syntax (name := cakePrimitive) "cake_primitive " term:max term:max (" assuming " term:max)? " by " tacticSeq : command

@[command_elab cakePrimitive] def elabCakePrimitive : CommandElab := fun stx => do
  let k := stx[1]
  let b := stx[2]
  let assm := stx[3]
  let tac : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨stx[5]⟩
  liftTermElabM do
    let key ← instantiateMVars (← elabTerm k none)
    synthesizeSyntheticMVarsNoPostponing
    let key ← instantiateMVars key
    if (getUnit? (← getEnv) key).isSome then throwError "{key} already has a unit"
    let body ← instantiateMVars (← elabTerm b (mkConst ``Exp))
    synthesizeSyntheticMVarsNoPostponing
    let assumes ← if assm.getNumArgs > 0 then do
        let a ← elabTerm assm[1] (mkSort .zero)
        synthesizeSyntheticMVarsNoPostponing
        pure #[← instantiateMVars a]
      else pure #[]
    let (uname, cname) ← freshUnit
    addDecl (Declaration.defnDecl (mkDefinitionValEx (uname ++ `body) [] (mkConst ``Exp) (← instantiateMVars body)
      .abbrev .safe []))
    let stmt ← primitiveStatement key (mkConst (uname ++ `body)) cname assumes
    let mvar ← mkFreshExprMVar stmt
    let remaining ← Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
    unless remaining.isEmpty do throwError "primitive certificate for {key} not proved"
    let pf ← instantiateMVars mvar
    addDecl (Declaration.thmDecl (mkTheoremValEx (uname ++ `cert) [] stmt pf []))
    let isFn : Bool ← forallTelescope (← inferType key) fun xs _ => pure (decide (xs.size > 0))
    let kind := if isFn then UnitKind.function "p" (uname ++ `body) false else .thunk "p" (uname ++ `body)
    addUnit { key, name := uname, cname, kind, cert := uname ++ `cert, datatypes := #[], deps := #[], assumes }

/-- `cake_replace K K' thm` with `thm : ∀ xs, K xs = K' xs`. -/
elab "cake_replace " k:ident r:ident thm:ident : command => do
  let kc ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo k
  let rc ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo r
  let tc ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thm
  liftTermElabM do
    let us := ((← getConstInfo tc).levelParams).map Level.param
    -- a monomorphic theorem may state the replacement of a universe-polymorphic
    -- `K` at universe 0; it then applies to the occurrences of `K` at universe 0
    let kLevels := (← getConstInfo kc).levelParams
    let rLevels := (← getConstInfo rc).levelParams
    let kus := if us.isEmpty then kLevels.map fun _ => levelZero else us
    let rus := if us.isEmpty then rLevels.map fun _ => levelZero else us
    let ok ← forallTelescope (← inferType (mkConst tc us)) fun xs ty => do
      let some (_, l, rr) := ty.eq? | return false
      return l == mkAppN (mkConst kc kus) xs && rr == mkAppN (mkConst rc rus) xs
    unless ok do throwError "{tc} must state ∀ xs, {kc} xs = {rc} xs (same universe parameters, in order)"
  modifyEnv fun env => replaceExt.addEntry env (kc, rc, tc)

/-- `cake_state_ref T`: computations `StateT T (Except ε) α` are translated as
functions of a reference holding the state (`MRET`, `ConPastel.Translator.EvalM`). -/
elab "cake_state_ref " t:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  modifyEnv fun env => stateRefExt.addEntry env c

/-- `cake_state_array T`: computations `StateT (Array T) (Except ε) α` are
translated over a CakeML `Array.array` holding the state (read with `getsD`,
written in place with `setM`). -/
elab "cake_state_array " t:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  modifyEnv fun env => stateArrExt.addEntry env c

/-- `cake_state_record T a₁ … aₙ with p`: computations `StateT T (Except ε) α`
are translated over a state record (`recRel`) whose hash-map fields `aᵢ : T →
Std.HashMap K V` are tables updated in place, and whose plain part is `p : T → P`.
Its map operations are `hmFind`, `hmInsertD`, `hmSize`, `hmClear` and `stRead`
(`ConPastel.Translator.StateOps`); a whole-state `get`/`set` is not translated. -/
syntax "cake_state_record " ident (colGt term:max)+ " with " term:max : command

elab_rules : command
  | `(cake_state_record $t:ident $accs* with $p) => do
    let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
    let info ← liftTermElabM do
      let σ := Lean.mkConst c
      let mut accNames : Array Name := #[]
      let mut entries : Array (Expr × Expr × Expr × Name) := #[]
      for a in accs, idx in [0:accs.size] do
        let ty ← mkArrow σ (← mkFreshTypeMVar)
        let e ← Term.elabTermEnsuringType a ty
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        let ety ← instantiateMVars (← inferType e)
        let hm ← forallTelescope ety fun _ b => whnfR b
        unless hm.isAppOfArity ``Std.HashMap 4 do throwError "cake_state_record: {a} is not a hash-map field"
        let K := hm.getArg! 0
        let V := hm.getArg! 1
        let nm := c ++ Name.mkSimple s!"cakeAcc{idx}"
        addDecl (Declaration.defnDecl (mkDefinitionValEx nm [] ety e .abbrev .safe []))
        setReducibleAttribute nm
        accNames := accNames.push nm
        let bkt := mkApp2 (Lean.mkConst ``Std.DHashMap.Internal.AssocList [levelZero, levelZero]) K
          (← withLocalDeclD `x K fun x => mkLambdaFVars #[x] V)
        let BI ← invOf bkt
        entries := entries.push (K, V, BI, nm)
      let pty ← mkArrow σ (← mkFreshTypeMVar)
      let pe ← Term.elabTermEnsuringType p pty
      Term.synthesizeSyntheticMVarsNoPostponing
      let pe ← instantiateMVars pe
      let pety ← instantiateMVars (← inferType pe)
      let pnm := c ++ `cakePlainAcc
      addDecl (Declaration.defnDecl (mkDefinitionValEx pnm [] pety pe .abbrev .safe []))
      setReducibleAttribute pnm
      let pT ← forallTelescope pety fun _ b => pure b
      let PI ← invOf pT
      -- the tables
      let tabsTy ← mkArrow σ (← mkAppM ``List #[Lean.mkConst ``ConPastel.Translator.TEntry])
      let tabsV ← withLocalDeclD `st σ fun st => do
        let es ← entries.toList.mapM fun (K, V, BI, nm) => do
          let raw ← mkAppM ``Std.DHashMap.inner #[← mkAppM ``Std.HashMap.inner #[mkApp (Lean.mkConst nm) st]]
          pure (mkAppN (Lean.mkConst ``ConPastel.Translator.TEntry.mk) #[K, V, BI, raw])
        mkLambdaFVars #[st] (← mkListLit (Lean.mkConst ``ConPastel.Translator.TEntry) es)
      let tnm := c ++ `cakeTabs
      addDecl (Declaration.defnDecl (mkDefinitionValEx tnm [] tabsTy tabsV .abbrev .safe []))
      setReducibleAttribute tnm
      -- the plain part
      let plainTy ← mkArrow σ (← mkArrow (Lean.mkConst ``Value) (mkSort levelZero))
      let plainV ← withLocalDeclD `st σ fun st => withLocalDeclD `v (Lean.mkConst ``Value) fun v => do
        mkLambdaFVars #[st, v] (mkApp2 PI (mkApp (Lean.mkConst pnm) st) v)
      let plnm := c ++ `cakePlain
      addDecl (Declaration.defnDecl (mkDefinitionValEx plnm [] plainTy plainV .abbrev .safe []))
      setReducibleAttribute plnm
      pure ({ tabs := tnm, plain := plnm, accs := accNames, plainAcc := pnm } : StateRecInfo)
    modifyEnv fun env => stateRecExt.addEntry env (c, info)

/-- `cake_state_swap T [i₁, …] [j₁, …]`: on the state record `T`, `swapRun enter
leave x` runs `x` with field `iₖ` holding field `jₖ`'s table and field `jₖ` a
fresh empty one, and moves them back afterwards (`EvalM_swapL`; `enter` and
`leave` must change the tables exactly so, which is checked by computation). -/
syntax "cake_state_swap " ident "[" num,* "]" "[" num,* "]" : command

elab_rules : command
  | `(cake_state_swap $t:ident [$is,*] [$js,*]) => do
    let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
    let some info := (stateRecExt.getState (← getEnv)).find? c
      | throwError "cake_state_swap: {c} is not a state record"
    let is := is.getElems.map (·.getNat)
    let js := js.getElems.map (·.getNat)
    unless is.size == js.size do throwError "cake_state_swap: lists of different lengths"
    modifyEnv fun env => stateRecExt.addEntry env (c, { info with swap := is.zip js })

/-- `cake_ghost T`: the closed type `T` becomes a ghost type (`GHOST T`). -/
elab "cake_ghost " t:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  modifyEnv fun env => ghostExt.addEntry env c

/-- `cake_replace_assuming K K' P` with `P : Prop` closed, `∀ xs, K xs = K' xs`. -/
elab "cake_replace_assuming " k:ident r:ident p:term : command => do
  let kc ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo k
  let rc ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo r
  let P ← liftTermElabM do
    let P ← instantiateMVars (← elabTerm p (mkSort .zero))
    synthesizeSyntheticMVarsNoPostponing
    let P ← instantiateMVars P
    let ok ← forallTelescope P fun xs ty => do
      let some (_, l, rr) := ty.eq? | return false
      return l == mkAppN (mkConst kc) xs && rr == mkAppN (mkConst rc) xs
    unless ok do throwError "{P} must state ∀ xs, {kc} xs = {rc} xs"
    pure P
  modifyEnv fun env => assumeReplaceExt.addEntry env (kc, rc, P)

/-- `cake_alias A B "full.name"`: `A` an abbreviation of the (possibly private)
constant `full.name`, and `B` a theorem stating its unfolding equation (to
prove replacements of private library functions). -/
elab "cake_alias " a:ident b:ident n:str : command => do
  let src := n.getString.toName
  liftTermElabM do
    let ci ← getConstInfo src
    let us := ci.levelParams.map Level.param
    addDecl (Declaration.defnDecl (mkDefinitionValEx a.getId ci.levelParams ci.type (mkConst src us) .abbrev .safe []))
    setReducibleAttribute a.getId
    let some eqn ← getUnfoldEqnFor? src (nonRec := true) | throwError "no unfolding equation for {src}"
    let eci ← getConstInfo eqn
    addDecl (Declaration.thmDecl (mkTheoremValEx b.getId eci.levelParams eci.type
      (mkConst eqn (eci.levelParams.map Level.param)) []))

/-- `cake_rewrite thm` with `thm : ∀ xs, lhs = rhs`: translate terms matching `lhs` as `rhs`. -/
elab "cake_rewrite " thm:ident : command => do
  let tc ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thm
  let head ← liftTermElabM do
    let ci ← getConstInfo tc
    forallTelescope ci.type fun _ ty => do
      let some (_, l, _) := ty.eq? | throwError "{tc} must be an equation"
      let .const c _ := l.getAppFn | throwError "{tc}: left-hand side must be a constant application"
      pure c
  modifyEnv fun env => rewriteExt.addEntry env (head, tc)

/-- `cake_module "tag"`: the units of this module get names of their own
(`ConPastel.Cake.tag.uk`, CakeML `%tag.k`), so that independent modules over a
common base can be imported together; such modules register no datatypes. -/
elab "cake_module " t:str : command => do
  modifyEnv fun env => cakeTagExt.setState env (some t.getString)

end ConPastel.Translator.Meta
