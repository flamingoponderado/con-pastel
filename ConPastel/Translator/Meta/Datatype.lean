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
  let env ← getEnv
  match Parser.runParserCategory env `command src with
  | .error e => throwError "generated source does not parse: {e}\n{src}"
  | .ok stx => elabCommand stx

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
  let cname (c : Name) : String := s!"t{stamp}.{c.componentsRev.head!}"
  let ms (s : String) : String := s!"(Flapjack.Basis.Pure.MlString.ofString {strLit s})"
  let fieldInv (i j : Nat) : String :=
    if (ctors[i]!.2)[j]!.1 == τ then s!"{N}.cakeInv" else s!"{N}.f{i}_{j}"
  let dataIdx (i : Nat) : List Nat := (List.range (ctors[i]!.2).size).filter fun j => (ctors[i]!.2)[j]!.2
  let under := String.join (List.replicate np "_ ")
  let pat (i : Nat) : String :=
    let (c, fs) := ctors[i]!
    s!"@{escName c} {under}{" ".intercalate ((List.range fs.size).map (s!"a{·}"))}"
  let convText (i : Nat) : String :=
    s!".conv (some (.typeStamp {ms (cname ctors[i]!.1)} {stamp})) [{", ".intercalate ((dataIdx i).map (s!"w{·}"))}]"
  -- the invariant
  let arms := (List.range ctors.size).map fun i =>
    let ds := dataIdx i
    let conds := ds.map fun j => s!"{fieldInv i j} a{j} w{j}"
    let body := " ∧ ".intercalate (conds ++ [s!"v = {convText i}"])
    let ex := if ds.isEmpty then body else s!"∃ {" ".intercalate (ds.map (s!"w{·}"))}, {body}"
    s!"  | {pat i}, v => {ex}"
  runCmd s!"def _root_.{N}.stamp : Nat := {stamp}"
  runCmd s!"open ConPastel.Translator Flapjack.SemanticPrimitivesHOL in\ndef _root_.{N}.cakeInv : RefInv {N}.ty\n{"\n".intercalate arms}"
  -- the constructor environment
  let lookups := (List.range ctors.size).map fun i =>
    s!"Flapjack.NamespaceHOL.nsLookup envC (.short {ms (cname ctors[i]!.1)}) = some ({(dataIdx i).length}, .typeStamp {ms (cname ctors[i]!.1)} {stamp})"
  runCmd s!"open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL in\ndef _root_.{N}.cakeHasCons (envC : Flapjack.NamespaceHOL.Namespace ModN ConN (Nat × Stamp)) : Prop :=\n  {" ∧ ".intercalate lookups}"
  let nC := ctors.size
  let proj (k : Nat) : String :=
    if nC == 1 then "hc" else
    if k + 1 == nC then "hc" ++ String.join (List.replicate k ".2") else
    "hc" ++ String.join (List.replicate k ".2") ++ ".1"
  -- constructor lemmas
  for i in [0:nC] do
    let (_, fs) := ctors[i]!
    let ds := dataIdx i
    let n := ds.length
    let hyps := ds.map fun j => s!"(h{j} : Eval env e{j} ({fieldInv i j} a{j}))"
    let evalAll := String.join (ds.reverse.map (s!"⟨h{·}, ")) ++ "trivial" ++ String.join (List.replicate n "⟩")
    let ps := "[" ++ ", ".intercalate (ds.reverse.map fun j => s!"{fieldInv i j} a{j}") ++ "]"
    let patL := if n == 0 then ".nil" else
      String.join (ds.reverse.map (s!".cons h{·}' (")) ++ ".nil" ++ String.join (List.replicate n ")")
    let wsRev := "[" ++ ", ".intercalate (ds.reverse.map (s!"w{·}")) ++ "]"
    let witness := if n == 0 then s!"by subst hv; simp [{N}.cakeInv]" else
      s!"by subst hv; simp only [{N}.cakeInv]; exact ⟨{", ".intercalate (ds.map (s!"w{·}"))}, {", ".intercalate (ds.map (s!"h{·}'"))}, by simp⟩"
    -- peel the value list field by field (a single `match` does not scale to many fields)
    let peel := if n == 0 then s!"match vs, hvs with\n  | {wsRev}, {patL} => exact {witness}" else
      String.join (ds.reverse.map (s!"rcases hvs with _ | ⟨h{·}', hvs⟩\n  ")) ++
      s!"rcases hvs with ⟨⟩\n  subst hv; simp only [{N}.cakeInv]; exact ⟨{", ".intercalate (ds.map fun _ => "_")}, {", ".intercalate (ds.map (s!"h{·}'"))}, by simp⟩"
    let allA := if fs.size == 0 then "" else "{" ++ " ".intercalate ((List.range fs.size).map (s!"a{·}")) ++ " : _}"
    let es := if n == 0 then "" else "{" ++ " ".intercalate (ds.map (s!"e{·}")) ++ " : Exp}"
    runCmd s!"set_option maxHeartbeats 0 in
open ConPastel.Translator Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.NamespaceHOL in
theorem _root_.{N}.con{i} {"{"}env : SemEnv Value{"}"} (hc : {N}.cakeHasCons env.c) {es} {allA}
    {" ".intercalate hyps} :
    Eval env (.con (some (.short {ms (cname ctors[i]!.1)})) [{", ".intercalate (ds.map (s!"e{·}"))}])
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
    let ds := dataIdx k
    let ns := ds.map (s!"n{k}_{·}")
    let as := (List.range fs.size).map (s!"a{·}")
    if !ns.isEmpty then params := params.push s!"({" ".intercalate ns} : VarN)"
    params := params.push s!"(hnd{k} : ([{", ".intercalate ns}] : List VarN).Nodup) (b{k} : Exp)"
    let invHyps := String.join (ds.map fun j => s!"{fieldInv k j} a{j} w{j} → ")
    let quant := if as.isEmpty then "" else s!"∀ {" ".intercalate as}, "
    let quantW := if ds.isEmpty then "" else s!"∀ {" ".intercalate (ds.map (s!"w{·}"))}, "
    params := params.push s!"(h{k} : {quant}x = {pat k} → {quantW}{invHyps}Eval (clauseEnv env ([{", ".intercalate ns}] : List VarN) ([{", ".intercalate (ds.map (s!"w{·}"))}] : List Value)) b{k} (Q ({pat k})))"
    casesL := casesL.push s!"({ms (cname c)}, ([{", ".intercalate ns}] : List VarN), b{k})"
    let obtainPat := if ds.isEmpty then "rfl" else s!"⟨{", ".intercalate (ds.map (s!"w{·}"))}, {", ".intercalate (ds.map (s!"hw{·}"))}, rfl⟩"
    arms2 := arms2.push s!"  | {escName (Name.mkSimple (c.componentsRev.head!.toString))} {" ".intercalate as} =>
    simp only [{N}.cakeInv] at hv
    obtain {obtainPat} := hv
    exact ⟨_, _, _, ([{", ".intercalate (ds.map (s!"w{·}"))}] : List Value), by simp, rfl, rfl,
      h{k} {" ".intercalate as} rfl {" ".intercalate (ds.map (s!"w{·}"))} {" ".intercalate (ds.map (s!"hw{·}"))}⟩"
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
  modifyEnv fun env => datatypeExt.addEntry env
    { ty := τ, name := N, stamp, ctors := ctors.map fun (c, fs) => (c, cname c, fs.map (·.2)) }

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
