import ConPastel.Translator.Meta.Goal
import ConPastel.Translator.Meta.Unit
import ConPastel.Translator.Meta.Ext
import ConPastel.Translator.List

/-!
# CakeML datatypes for closed Lean inductive types

`registerDatatype τ` generates, for a closed inductive type `τ` (an instance
of a parameterized type, or a plain inductive), declarations under a fresh
namespace `N = ConPastel.CakeT.tK`:

* `N.ty := τ` (reducible), so generated source never prints types;
* `N.f_i_j : RefInv _`, the invariant of data field `j` of constructor `i`;
* `N.cakeInv : RefInv N.ty`, by structural recursion;
* `N.cakeHasCons envC`, that `envC` declares the constructors;
* `N.con_i`: evaluating constructor `i` on representations of its data fields;
* `N.cake_mat`: a flat match on a representation of `x : N.ty` runs the clause
  of `x`'s constructor, with the path condition `x = C fields`.

Proof and type fields are erased: a CakeML constructor takes only the data
fields. Type stamps are assigned in registration order, from 2.
-/

namespace ConPastel.Translator.Meta
open Lean Meta Elab Command

def runCmd (src : String) : CommandElabM Unit := do
  if (← IO.getEnv "CAKE_SHOW_SRC").isSome then logInfo src
  let env ← getEnv
  match Parser.runParserCategory env `command src with
  | .error e => throwError "generated source does not parse: {e}\n{src}"
  | .ok stx =>
    let before := (← get).messages.toList.filter (·.severity == .error) |>.length
    elabCommand stx
    let after := (← get).messages.toList.filter (·.severity == .error) |>.length
    if after > before then throwError "generated declaration failed to elaborate:\n{src}"

def addAbbrev (n : Name) (ty val : Expr) : MetaM Unit := do
  addDecl (Declaration.defnDecl (mkDefinitionValEx n [] ty val .abbrev .safe []))
  setReducibleAttribute n

/-- Fields of each constructor of `τ`: per field, its type and whether it is data. -/
def ctorFields (τ : Expr) : MetaM (Array (Name × Array (Expr × Bool))) := do
  let .const I lvls := τ.getAppFn | throwError "{τ} is not an inductive type"
  let some (.inductInfo ii) := (← getEnv).find? I | throwError "{τ} is not an inductive type"
  if ii.numIndices > 0 then throwError "indexed family {τ} not supported"
  if ii.all.length > 1 then throwError "mutual inductive {τ} not supported yet"
  let params := τ.getAppArgs
  ii.ctors.toArray.mapM fun c => do
    let cty ← instantiateTypeLevelParams (← getConstInfo c).toConstantVal lvls
    let cty ← instantiateForall cty params
    forallTelescope cty fun fs _ => do
      let infos ← fs.mapM fun f => do
        let fty := (← instantiateMVars (← inferType f)).headBeta
        let data := !(← isErasedType fty)
        if data && fty.hasAnyFVar (fs.contains <| .fvar ·) then
          throwError "field of {c} has a dependent type {fty}"
        return (fty, data)
      return (c, infos)

def strLit (s : String) : String := s.quote

/-- A name for generated source, every component escaped (constructor names
may be keywords, e.g. `opaque`). -/
def escName (n : Name) : String :=
  ".".intercalate (n.components.map fun c => match c with
    | .str _ s => "«" ++ s ++ "»"
    | .num _ k => toString k
    | .anonymous => "")

/-- The number of term parameters of a datatype key (`abstractType`). -/
def keyParams : Expr → Nat
  | .lam _ _ b _ => keyParams b + 1
  | _ => 0

/-- The type of a datatype key, under its parameters (loose bound variables). -/
def keyBody : Expr → Expr
  | .lam _ _ b _ => keyBody b
  | e => e

/-- The fields of each constructor of the datatype with key `τ`, the field
types abstracted over the key's parameters. -/
def ctorFieldsKey (τ : Expr) : MetaM (Array (Name × Array (Expr × Bool))) :=
  lambdaTelescope τ fun xs b => do
    let cs ← ctorFields b
    cs.mapM fun (c, fs) => return (c, ← fs.mapM fun (fty, d) => return (← mkLambdaFVars xs fty, d))

partial def registerDatatype (τ : Expr) (stack : List Expr := []) : CommandElabM Unit := do
  let τ ← liftTermElabM (lambdaTelescope τ fun xs b => do mkLambdaFVars xs (← normType b))
  if (getDatatypeByType? (← getEnv) τ).isSome then return
  if stack.contains τ then throwError "cyclic datatype dependency at {τ} (mutual types are not supported yet)"
  let nparams := keyParams τ
  -- the invariant of a field type (abstracted over the parameters), under them
  let fieldInvL (ftyL : Expr) : MetaM Expr := lambdaTelescope τ fun xs _ => do
    mkLambdaFVars xs (← invOf (ftyL.beta xs))
  -- first the datatypes the field invariants need
  let ctors₀ ← liftTermElabM (ctorFieldsKey τ)
  for (_, fs) in ctors₀ do
    for (fty, data) in fs do
      if data && fty != τ then
        repeat
          needDatatypeRef.set none
          try
            let _ ← liftTermElabM (fieldInvL fty)
            break
          catch e =>
            match ← needDatatypeRef.get with
            | some τ' => registerDatatype τ' (τ :: stack)
            | none => throw e
  let env ← getEnv
  if let some t := cakeTagExt.getState env then
    throwError "datatype {τ} is needed by module '{t}': register it in the base chain (cake_datatype)"
  let stamp := nextStamp env
  logInfo m!"cake datatype t{stamp}: {τ} ({(← liftTermElabM (ctorFieldsKey τ)).size} constructors)"
  cakeLog s!"[cake] datatype t{stamp}: {← liftTermElabM (do return (← ppExpr τ).pretty.take 120)}"
  let N := Name.mkStr `ConPastel.CakeT s!"t{stamp}"
  let .const I _ := (keyBody τ).getAppFn | throwError "{τ} is not an inductive type"
  let some (.inductInfo ii) := env.find? I | throwError "{τ} is not an inductive type"
  let np := ii.numParams
  let ctors ← liftTermElabM (ctorFieldsKey τ)
  -- the type and the field invariants (over the parameters, for a family)
  liftTermElabM do
    addAbbrev (N ++ `ty) (← inferType τ) τ
    for i in [0:ctors.size] do
      let (_, fs) := ctors[i]!
      for j in [0:fs.size] do
        let (fty, data) := fs[j]!
        if data && fty != τ then
          let ity ← lambdaTelescope τ fun xs _ => do
            mkForallFVars xs (← mkAppM ``ConPastel.Translator.RefInv #[fty.beta xs])
          addAbbrev (N ++ Name.mkSimple s!"f{i}_{j}") ity (← fieldInvL fty)
  -- cached computed fields (`cake_cached`): stored first in every constructor
  let cfs := getCached env I
  if !cfs.isEmpty && np != 0 then throwError "cached fields of the parameterized type {τ} are not supported"
  let m := cfs.size
  liftTermElabM do
    for k in [0:m] do
      let cty ← inferType (mkConst cfs[k]!)
      let .forallE _ _ rty _ := cty | throwError "cached field {cfs[k]!} is not a function"
      if rty.hasLooseBVars then throwError "cached field {cfs[k]!} has a dependent type"
      addAbbrev (N ++ Name.mkSimple s!"c{k}") (← mkAppM ``ConPastel.Translator.RefInv #[rty]) (← invOf rty)
  let cname (c : Name) : String := s!"t{stamp}.{c.componentsRev.head!}"
  let ms (s : String) : String := s!"(Flapjack.Basis.Pure.MlString.ofString {strLit s})"
  -- a family's parameters: explicit in the definitions, implicit in the theorems
  let ps := (List.range nparams).map (s!"x{·}")
  let ap := String.join (ps.map (" " ++ ·))
  let bsE := String.join (ps.map (s!" ({·} : _)"))
  let bsI := String.join (ps.map fun x => " {" ++ x ++ " : _}")
  let fieldInv (i j : Nat) : String :=
    if (ctors[i]!.2)[j]!.1 == τ then s!"{N}.cakeInv{ap}" else s!"{N}.f{i}_{j}{ap}"
  let dataIdx (i : Nat) : List Nat := (List.range (ctors[i]!.2).size).filter fun j => (ctors[i]!.2)[j]!.2
  let under := String.join (List.replicate np "_ ")
  let pat (i : Nat) : String :=
    let (c, fs) := ctors[i]!
    s!"@{escName c} {under}{" ".intercalate ((List.range fs.size).map (s!"a{·}"))}"
  -- the stored items of constructor `i`: cached fields `zk`, then data fields `j`,
  -- each with the invariant its value satisfies
  let items (i : Nat) : List (String × String) :=
    (List.range m).map (fun k => (s!"z{k}", s!"{N}.c{k} ({escName cfs[k]!} ({pat i}))")) ++
    (dataIdx i).map (fun j => (s!"{j}", s!"{fieldInv i j} a{j}"))
  let convText (i : Nat) : String :=
    s!".conv (some (.typeStamp {ms (cname ctors[i]!.1)} {stamp})) [{", ".intercalate ((items i).map (s!"w{·.1}"))}]"
  -- the invariant
  let arms := (List.range ctors.size).map fun i =>
    let its := items i
    let conds := its.map fun (x, inv) => s!"{inv} w{x}"
    let body := " ∧ ".intercalate (conds ++ [s!"v = {convText i}"])
    let ex := if its.isEmpty then body else s!"∃ {" ".intercalate (its.map (s!"w{·.1}"))}, {body}"
    s!"  | {pat i}, v => {ex}"
  runCmd s!"def _root_.{N}.stamp : Nat := {stamp}"
  runCmd s!"open ConPastel.Translator Flapjack.SemanticPrimitivesHOL in\ndef _root_.{N}.cakeInv{bsE} : RefInv ({N}.ty{ap})\n{"\n".intercalate arms}"
  -- the constructor environment
  let lookups := (List.range ctors.size).map fun i =>
    s!"Flapjack.NamespaceHOL.nsLookup envC (.short {ms (cname ctors[i]!.1)}) = some ({(items i).length}, .typeStamp {ms (cname ctors[i]!.1)} {stamp})"
  runCmd s!"open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL in\ndef _root_.{N}.cakeHasCons (envC : Flapjack.NamespaceHOL.Namespace ModN ConN (Nat × Stamp)) : Prop :=\n  {" ∧ ".intercalate lookups}"
  let nC := ctors.size
  let proj (k : Nat) : String :=
    if nC == 1 then "hc" else
    if k + 1 == nC then "hc" ++ String.join (List.replicate k ".2") else
    "hc" ++ String.join (List.replicate k ".2") ++ ".1"
  -- constructor lemmas: the stored items' expressions, in order
  for i in [0:nC] do
    let (_, fs) := ctors[i]!
    let its := items i
    let xs := its.map (·.1)
    let n := its.length
    let hyps := its.map fun (x, inv) => s!"(h{x} : Eval env e{x} ({inv}))"
    let evalAll := String.join (xs.reverse.map (s!"⟨h{·}, ")) ++ "trivial" ++ String.join (List.replicate n "⟩")
    let ps := "[" ++ ", ".intercalate (its.reverse.map (·.2)) ++ "]"
    let patL := if n == 0 then ".nil" else
      String.join (xs.reverse.map (s!".cons h{·}' (")) ++ ".nil" ++ String.join (List.replicate n ")")
    let wsRev := "[" ++ ", ".intercalate (xs.reverse.map (s!"w{·}")) ++ "]"
    let witness := if n == 0 then s!"by subst hv; simp [{N}.cakeInv]" else
      s!"by subst hv; simp only [{N}.cakeInv]; exact ⟨{", ".intercalate (xs.map (s!"w{·}"))}, {", ".intercalate (xs.map (s!"h{·}'"))}, by simp⟩"
    -- peel the value list item by item (a single `match` does not scale to many fields)
    let peel := if n == 0 then s!"match vs, hvs with\n  | {wsRev}, {patL} => exact {witness}" else
      String.join (xs.reverse.map (s!"rcases hvs with _ | ⟨h{·}', hvs⟩\n  ")) ++
      s!"rcases hvs with ⟨⟩\n  subst hv; simp only [{N}.cakeInv]; exact ⟨{", ".intercalate (xs.map fun _ => "_")}, {", ".intercalate (xs.map (s!"h{·}'"))}, by simp⟩"
    let allA := if fs.size == 0 then "" else "{" ++ " ".intercalate ((List.range fs.size).map (s!"a{·}")) ++ " : _}"
    let es := if n == 0 then "" else "{" ++ " ".intercalate (xs.map (s!"e{·}")) ++ " : Exp}"
    runCmd s!"set_option maxHeartbeats 0 in
open ConPastel.Translator Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.NamespaceHOL in
theorem _root_.{N}.con{i}{bsI} {"{"}env : SemEnv Value{"}"} (hc : {N}.cakeHasCons env.c) {es} {allA}
    {" ".intercalate hyps} :
    Eval env (.con (some (.short {ms (cname ctors[i]!.1)})) [{", ".intercalate (xs.map (s!"e{·}"))}])
      ({N}.cakeInv{ap} (show {N}.ty{ap} from {pat i})) := by
  have hl := {proj i}
  refine Eval_weaken (Eval_con (Ps := {ps}) hl {evalAll}) ?_
  rintro v ⟨vs, hvs, hv⟩
  {peel}"
  -- the match lemma
  let mut params : Array String := #[]
  let mut casesL : Array String := #[]
  let mut arms2 : Array String := #[]
  for k in [0:nC] do
    let (c, fs) := ctors[k]!
    let its := items k
    let xs := its.map (·.1)
    let ns := xs.map (s!"n{k}_{·}")
    let as := (List.range fs.size).map (s!"a{·}")
    if !ns.isEmpty then params := params.push s!"({" ".intercalate ns} : VarN)"
    params := params.push s!"(hnd{k} : ([{", ".intercalate ns}] : List VarN).Nodup) (b{k} : Exp)"
    let invHyps := String.join (its.map fun (x, inv) => s!"{inv} w{x} → ")
    let quant := if as.isEmpty then "" else s!"∀ {" ".intercalate as}, "
    let quantW := if xs.isEmpty then "" else s!"∀ {" ".intercalate (xs.map (s!"w{·}"))}, "
    params := params.push s!"(h{k} : {quant}x = {pat k} → {quantW}{invHyps}Eval (clauseEnv env ([{", ".intercalate ns}] : List VarN) ([{", ".intercalate (xs.map (s!"w{·}"))}] : List Value)) b{k} (Q ({pat k})))"
    casesL := casesL.push s!"({ms (cname c)}, ([{", ".intercalate ns}] : List VarN), b{k})"
    let obtainPat := if xs.isEmpty then "rfl" else s!"⟨{", ".intercalate (xs.map (s!"w{·}"))}, {", ".intercalate (xs.map (s!"hw{·}"))}, rfl⟩"
    arms2 := arms2.push s!"  | {escName (Name.mkSimple (c.componentsRev.head!.toString))} {" ".intercalate as} =>
    simp only [{N}.cakeInv] at hv
    obtain {obtainPat} := hv
    exact ⟨_, _, _, ([{", ".intercalate (xs.map (s!"w{·}"))}] : List Value), by simp, rfl, rfl,
      h{k} {" ".intercalate as} rfl {" ".intercalate (xs.map (s!"w{·}"))} {" ".intercalate (xs.map (s!"hw{·}"))}⟩"
  let lookupArms := String.join ((List.range nC).map fun k => s!"\n      · exact {proj k}")
  let nodupArms := String.join ((List.range nC).map fun k => s!"\n      · exact hnd{k}")
  let rcasesPat := " | ".intercalate ((List.range nC).map fun _ => "⟨rfl, rfl, rfl⟩")
  runCmd s!"set_option maxHeartbeats 0 in
open ConPastel.Translator Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.NamespaceHOL in
theorem _root_.{N}.cake_mat{bsI} {"{"}env : SemEnv Value{"}"} (hc : {N}.cakeHasCons env.c)
    {"{"}e : Exp{"}"} {"{"}x : {N}.ty{ap}{"}"} (he : Eval env e ({N}.cakeInv{ap} x)) {"{"}Q : {N}.ty{ap} → Value → Prop{"}"}
    {" ".intercalate params.toList} :
    Eval env (.mat e (conClauses [{", ".intercalate casesL.toList}])) (Q x) := by
  have hf : FlatCases env.c {stamp} [{", ".intercalate casesL.toList}] := by
    refine ⟨?_, by simp only [List.map_cons, List.map_nil]; decide, ?_⟩
    · intro c xs b hm
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with {rcasesPat}{lookupArms}
    · intro c xs b hm
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with {rcasesPat}{nodupArms}
  refine Eval_mat hf he ?_
  intro v hv
  cases x with
{"\n".intercalate arms2.toList}"
  -- reading a cached field: a match whose every clause returns the stored value
  for c in [0:m] do
    let mut args : Array String := #[]
    let mut casesC : Array String := #[]
    for k in [0:nC] do
      let (cn, fs) := ctors[k]!
      let its := items k
      let xs := its.map (·.1)
      let vn (x : String) : String := ms s!"c{x}"
      let as := (List.range fs.size).map (s!"a{·}")
      args := args ++ (xs.map vn).toArray
      args := args.push "(by decide)"
      args := args.push s!"(Exp.var (.short {vn s!"z{c}"}))"
      let binders := " ".intercalate (as ++ ["_"] ++ xs.map (s!"w{·}") ++ xs.map (s!"hw{·}"))
      args := args.push s!"(fun {binders} => Eval_var _ _ _ _ (by simp +decide [clauseEnv, nsLookup_nsAppend_alist_short, List.lookup, beq_eq_decide_of_decEq]) hwz{c})"
      casesC := casesC.push s!"({ms (cname cn)}, ([{", ".intercalate (xs.map vn)}] : List VarN), Exp.var (.short {vn s!"z{c}"}))"
    runCmd s!"set_option maxHeartbeats 0 in
open ConPastel.Translator Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.NamespaceHOL in
theorem _root_.{N}.cake_cf{c}{bsI} {"{"}env : SemEnv Value{"}"} (hc : {N}.cakeHasCons env.c)
    {"{"}e : Exp{"}"} {"{"}x : {N}.ty{ap}{"}"} (he : Eval env e ({N}.cakeInv{ap} x)) :
    Eval env (.mat e (conClauses [{", ".intercalate casesC.toList}])) ({N}.c{c} ({escName cfs[c]!} x)) :=
  {N}.cake_mat (Q := fun x => {N}.c{c} ({escName cfs[c]!} x)) hc he {" ".intercalate args.toList}"
  modifyEnv fun env => datatypeExt.addEntry env
    { ty := τ, name := N, stamp, ctors := ctors.map fun (c, fs) => (c, cname c, fs.map (·.2)), cached := cfs,
      nparams }

/-- Translate `key` (and what it needs), registering the datatypes it needs. -/
partial def cakeUnitCmd (key : Expr) : CommandElabM Unit := do
  repeat
    needDatatypeRef.set none
    try
      liftTermElabM (translateUnit key)
      return
    catch e =>
      match ← needDatatypeRef.get with
      | some τ => registerDatatype τ
      | none => throw e

elab "cake_unit " ts:(colGt term:max)+ : command => do
  for t in ts do
    let key ← liftTermElabM do
      let key ← instantiateMVars (← Term.elabTerm t none)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars key
    cakeUnitCmd key

initialize datatypeHookRef.set fun τ => liftCommandElabM (registerDatatype τ)

/-- `cake_prepass f`: translate the dependencies of `f`'s mutual block (not the
block itself), e.g. in a stage module that later modules import. -/
elab "cake_prepass " t:term:max : command => do
  let key ← liftTermElabM do
    let key ← instantiateMVars (← Term.elabTerm t none)
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars key
  repeat
    needDatatypeRef.set none
    try
      let _ ← liftTermElabM (prepassBlock key)
      return
    catch e =>
      match ← needDatatypeRef.get with
      | some τ => registerDatatype τ
      | none => throw e

/-- Run `k` with the split mode of the mutual block of `c` set. -/
def withSplitMode (c : Name) (m : SplitMode) (k : CommandElabM Unit) : CommandElabM Unit := do
  mutualSplitRef.set (some (c, m))
  try k finally mutualSplitRef.set none

def elabUnitKey (t : Term) : CommandElabM Expr := liftTermElabM do
  let key ← instantiateMVars (← Term.elabTerm t none)
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars key

/-- `cake_mutual_prepare f d₁ … dₖ`: the first stage of translating the mutual
block of `f` in several modules, so that Lake solves its members in separate
processes:

```
cake_mutual_prepare f d₁ … dₖ   -- module B: dependencies, shared declarations
cake_mutual_part f j n          -- modules P₀ … Pₙ₋₁ (each imports B): members i % n = j
cake_mutual_finish f            -- module F (imports every Pⱼ): the joint theorem
```

It translates the block's dependencies (the pre-pass) and the units `dᵢ`, which
become extra dependencies of the block: those its members need that the
pre-pass does not find (a part reports them). -/
elab "cake_mutual_prepare " t:term:max ds:(colGt term:max)* : command => do
  let key ← elabUnitKey t
  let .const c _ := key.getAppFn | throwError "cake_mutual_prepare: {key} is not a constant"
  let extras ← ds.mapM elabUnitKey
  for d in extras do cakeUnitCmd d
  modifyEnv fun env => splitExtraExt.addEntry env (c, extras)
  withSplitMode c .prepare (cakeUnitCmd key)

/-- `cake_mutual_part f j n`: solve the members `i` of `f`'s block with
`i % n = j` (see `cake_mutual_prepare`). -/
elab "cake_mutual_part " t:term:max j:num n:num : command => do
  let key ← elabUnitKey t
  let .const c _ := key.getAppFn | throwError "cake_mutual_part: {key} is not a constant"
  unless j.getNat < n.getNat do throwError "cake_mutual_part: need j < n"
  withSplitMode c (.part j.getNat n.getNat) (cakeUnitCmd key)

/-- `cake_mutual_finish f`: the joint theorem of `f`'s block and its members'
units, from the parts (see `cake_mutual_prepare`). -/
elab "cake_mutual_finish " t:term:max : command => do
  let key ← elabUnitKey t
  let .const c _ := key.getAppFn | throwError "cake_mutual_finish: {key} is not a constant"
  withSplitMode c .finish (cakeUnitCmd key)

/-- `cake_datatype T`: register the (closed) inductive type `T`. -/
elab "cake_datatype " t:term:max : command => do
  let τ ← liftTermElabM do
    let τ ← instantiateMVars (← Term.elabTerm t none)
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars τ
  registerDatatype τ

end ConPastel.Translator.Meta

namespace ConPastel.Translator.Meta
open Lean Meta Elab Command

/-- `cake_cached T f₁ … fₘ`: store the computed fields `fᵢ : T → _` in every
CakeML constructor of `T` (registered before `T` is translated). -/
elab "cake_cached " t:ident fs:(colGt ident)+ : command => do
  let I ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  if (allDatatypes (← getEnv)).any (fun d => d.ty.getAppFn.constName? == some I) then
    throwError "cake_cached: {I} is already translated"
  let fns ← fs.mapM fun f => liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  modifyEnv fun env => cachedExt.addEntry env (I, fns)

end ConPastel.Translator.Meta
