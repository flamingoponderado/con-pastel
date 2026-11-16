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

partial def registerDatatype (τ : Expr) (stack : List Expr := []) : CommandElabM Unit := do
  let τ ← liftTermElabM (normType τ)
  if (getDatatypeByType? (← getEnv) τ).isSome then return
  if stack.contains τ then throwError "cyclic datatype dependency at {τ} (mutual types are not supported yet)"
  -- first the datatypes the field invariants need
  let ctors₀ ← liftTermElabM (ctorFields τ)
  for (_, fs) in ctors₀ do
    for (fty, data) in fs do
      if data && fty != τ then
        repeat
          needDatatypeRef.set none
          try
            let _ ← liftTermElabM (invOf fty)
            break
          catch e =>
            match ← needDatatypeRef.get with
            | some τ' => registerDatatype τ' (τ :: stack)
            | none => throw e
  let env ← getEnv
  if let some t := cakeTagExt.getState env then
    throwError "datatype {τ} is needed by module '{t}': register it in the base chain (cake_datatype)"
  let stamp := nextStamp env
  logInfo m!"cake datatype t{stamp}: {τ} ({(← liftTermElabM (ctorFields τ)).size} constructors)"
  cakeLog s!"[cake] datatype t{stamp}: {← liftTermElabM (do return (← ppExpr τ).pretty.take 120)}"
  let N := Name.mkStr `ConPastel.CakeT s!"t{stamp}"
  let .const I _ := τ.getAppFn | throwError "{τ} is not an inductive type"
  let some (.inductInfo ii) := env.find? I | throwError "{τ} is not an inductive type"
  let np := ii.numParams
  let ctors ← liftTermElabM (ctorFields τ)
  -- the type and the field invariants
  liftTermElabM do
    addAbbrev (N ++ `ty) (← inferType τ) τ
    for i in [0:ctors.size] do
      let (_, fs) := ctors[i]!
      for j in [0:fs.size] do
        let (fty, data) := fs[j]!
        if data && fty != τ then
          addAbbrev (N ++ Name.mkSimple s!"f{i}_{j}") (← mkAppM ``ConPastel.Translator.RefInv #[fty]) (← invOf fty)
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
  let fieldInv (i j : Nat) : String :=
    if (ctors[i]!.2)[j]!.1 == τ then s!"{N}.cakeInv" else s!"{N}.f{i}_{j}"
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
  runCmd s!"open ConPastel.Translator Flapjack.SemanticPrimitivesHOL in\ndef _root_.{N}.cakeInv : RefInv {N}.ty\n{"\n".intercalate arms}"
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
theorem _root_.{N}.con{i} {"{"}env : SemEnv Value{"}"} (hc : {N}.cakeHasCons env.c) {es} {allA}
    {" ".intercalate hyps} :
    Eval env (.con (some (.short {ms (cname ctors[i]!.1)})) [{", ".intercalate (xs.map (s!"e{·}"))}])
      ({N}.cakeInv (show {N}.ty from {pat i})) := by
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
theorem _root_.{N}.cake_mat {"{"}env : SemEnv Value{"}"} (hc : {N}.cakeHasCons env.c)
    {"{"}e : Exp{"}"} {"{"}x : {N}.ty{"}"} (he : Eval env e ({N}.cakeInv x)) {"{"}Q : {N}.ty → Value → Prop{"}"}
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
theorem _root_.{N}.cake_cf{c} {"{"}env : SemEnv Value{"}"} (hc : {N}.cakeHasCons env.c)
    {"{"}e : Exp{"}"} {"{"}x : {N}.ty{"}"} (he : Eval env e ({N}.cakeInv x)) :
    Eval env (.mat e (conClauses [{", ".intercalate casesC.toList}])) ({N}.c{c} ({escName cfs[c]!} x)) :=
  {N}.cake_mat (Q := fun x => {N}.c{c} ({escName cfs[c]!} x)) hc he {" ".intercalate args.toList}"
  modifyEnv fun env => datatypeExt.addEntry env
    { ty := τ, name := N, stamp, ctors := ctors.map fun (c, fs) => (c, cname c, fs.map (·.2)), cached := cfs }

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
