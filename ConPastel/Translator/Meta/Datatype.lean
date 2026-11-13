import ConPastel.Translator.Meta.Goal
import ConPastel.Translator.Meta.Ext
import ConPastel.Translator.List

/-!
# `cake_datatype`: CakeML datatypes for Lean inductives

For an inductive `T` without indices or type parameters, generate (by
elaborating generated Lean source):

* `T.cakeStamp : Nat`, its CakeML type stamp;
* `T.cakeInv : RefInv T`, the refinement invariant, by structural recursion;
* `T.cakeHasCons envC`, that `envC` declares `T`'s constructors;
* for each constructor `C`, `C.cake_con`: evaluating `C`'s CakeML
  constructor on representations of its fields represents `C fields`;
* `T.cake_mat`: a flat match on a representation of `x : T` runs the clause
  of `x`'s constructor, with the path condition `x = C fields`.

Type stamps are assigned in registration order, starting after the
primitive types `bool` (0) and `list` (1).
-/

namespace ConPastel.Translator.Meta
open Lean Meta Elab Command

/-- The invariant (as source text) for a field type. -/
partial def invText (self : Name) (ty : Expr) : MetaM String := do
  let ty ← whnfR ty
  if ty.isConstOf ``Nat then return "NAT"
  if ty.isConstOf ``Int then return "INT"
  if ty.isConstOf ``Bool then return "BOOL"
  if ty.isConstOf self then return s!"{self}.cakeInv"
  if let .const n _ := ty then
    if (getDatatype? (← getEnv) n).isSome then return s!"{n}.cakeInv"
  if ty.isAppOfArity ``List 1 then
    return s!"(LIST {← invText self ty.appArg!})"
  throwError "no invariant for field type {ty}"

def runCmd (src : String) : CommandElabM Unit := do
  let env ← getEnv
  match Parser.runParserCategory env `command src with
  | .error e => throwError "generated source does not parse: {e}\n{src}"
  | .ok stx => elabCommand stx

def strLit (s : String) : String := s.quote

def cakeDatatype (T : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some (.inductInfo ii) := env.find? T | throwError "{T} is not an inductive type"
  unless ii.numParams == 0 && ii.numIndices == 0 do throwError "parameters/indices not supported yet"
  let stamp := nextStamp env
  -- constructors and field types
  let ctors ← liftTermElabM do ii.ctors.toArray.mapM fun c => do
    let ci ← getConstInfo c
    forallTelescope ci.type fun fs _ => do
      let tys ← fs.mapM fun f => do invText T (← inferType f)
      return (c, tys)
  let ctorName (c : Name) : String := strLit c.toString
  let convText (c : Name) (vs : List String) : String :=
    s!".conv (some (.typeStamp (Flapjack.Basis.Pure.MlString.ofString {ctorName c}) {stamp})) [{", ".intercalate vs}]"
  -- the invariant
  let arms := ctors.toList.map fun (c, tys) =>
    let xs := (List.range tys.size).map (s!"a{·}")
    let vs := (List.range tys.size).map (s!"w{·}")
    let pat := s!"| .{c.componentsRev.head!} {" ".intercalate xs}, v =>"
    let conds := (tys.toList.zip (xs.zip vs)).map fun (inv, x, w) => s!"{inv} {x} {w}"
    let body := " ∧ ".intercalate (conds ++ [s!"v = {convText c vs}"])
    let ex := if vs.isEmpty then body else s!"∃ {" ".intercalate vs}, {body}"
    s!"  {pat} {ex}"
  runCmd s!"def _root_.{T}.cakeStamp : Nat := {stamp}"
  runCmd s!"open ConPastel.Translator Flapjack.SemanticPrimitivesHOL in\ndef _root_.{T}.cakeInv : RefInv {T}\n{"\n".intercalate arms}"
  -- constructor environment
  let lookups := ctors.toList.map fun (c, tys) =>
    s!"Flapjack.NamespaceHOL.nsLookup envC (.short (Flapjack.Basis.Pure.MlString.ofString {ctorName c})) = some ({tys.size}, .typeStamp (Flapjack.Basis.Pure.MlString.ofString {ctorName c}) {stamp})"
  runCmd s!"open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL in\ndef _root_.{T}.cakeHasCons (envC : Flapjack.NamespaceHOL.Namespace ModN ConN (Nat × Stamp)) : Prop :=\n  {" ∧ ".intercalate lookups}"
  let nC := ctors.size
  -- projection of the k-th conjunct out of `cakeHasCons`
  let proj (k : Nat) : String :=
    if nC == 1 then "hc" else
    if k + 1 == nC then "hc" ++ String.join (List.replicate k ".2") else
    "hc" ++ String.join (List.replicate k ".2") ++ ".1"
  -- constructor lemmas
  for k in [0:nC] do
    let (c, tys) := ctors[k]!
    let n := tys.size
    let es := (List.range n).map (s!"e{·}")
    let as := (List.range n).map (s!"a{·}")
    let ws := (List.range n).map (s!"w{·}")
    let hyps := (List.range n).map fun i => s!"(h{i} : Eval env e{i} ({tys[i]!} a{i}))"
    let evalAll := String.join ((List.range n).reverse.map (s!"⟨h{·}, ")) ++ "trivial" ++ String.join (List.replicate n "⟩")
    let ps := "[" ++ ", ".intercalate ((List.range n).reverse.map fun i => s!"{tys[i]!} a{i}") ++ "]"
    let pat := if n == 0 then ".nil" else
      String.join ((List.range n).reverse.map (s!".cons h{·}' (")) ++ ".nil" ++ String.join (List.replicate n ")")
    let wsRev := "[" ++ ", ".intercalate ws.reverse ++ "]"
    let witness := if n == 0 then "by subst hv; simp [" ++ toString T ++ ".cakeInv]" else
      s!"by subst hv; simp only [{T}.cakeInv]; exact ⟨{", ".intercalate ws}, {", ".intercalate ((List.range n).map (s!"h{·}'"))}, by simp⟩"
    runCmd s!"open ConPastel.Translator Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.NamespaceHOL in
theorem _root_.{c}.cake_con {"{"}env : SemEnv Value{"}"} (hc : {T}.cakeHasCons env.c)
    {if n == 0 then "" else "{" ++ " ".intercalate es ++ " : Exp}"} {if n == 0 then "" else "{" ++ " ".intercalate as ++ " : _}"}
    {" ".intercalate hyps} :
    Eval env (.con (some (.short (Flapjack.Basis.Pure.MlString.ofString {ctorName c}))) [{", ".intercalate es}])
      ({T}.cakeInv ({c} {" ".intercalate as})) := by
  have hl := {proj k}
  refine Eval_weaken (Eval_con (Ps := {ps}) hl {evalAll}) ?_
  rintro v ⟨vs, hvs, hv⟩
  match vs, hvs with
  | {wsRev}, {pat} => exact {witness}"
  -- the match lemma
  let mut params : Array String := #[]
  let mut casesL : Array String := #[]
  let mut arms : Array String := #[]
  for k in [0:nC] do
    let (c, tys) := ctors[k]!
    let n := tys.size
    let ns := (List.range n).map (s!"n{k}_{·}")
    let as := (List.range n).map (s!"a{·}")
    let ws := (List.range n).map (s!"w{·}")
    if n > 0 then params := params.push s!"({" ".intercalate ns} : VarN)"
    params := params.push s!"(hnd{k} : ([{", ".intercalate ns}] : List VarN).Nodup) (b{k} : Exp)"
    let invHyps := String.join ((List.range n).map fun i => s!"{tys[i]!} a{i} w{i} → ")
    let quant := if n == 0 then "" else s!"∀ {" ".intercalate as}, "
    let quantW := if n == 0 then "" else s!"∀ {" ".intercalate ws}, "
    params := params.push s!"(h{k} : {quant}x = {c} {" ".intercalate as} → {quantW}{invHyps}Eval (clauseEnv env ([{", ".intercalate ns}] : List VarN) ([{", ".intercalate ws}] : List Value)) b{k} (Q ({c} {" ".intercalate as})))"
    casesL := casesL.push s!"(Flapjack.Basis.Pure.MlString.ofString {ctorName c}, ([{", ".intercalate ns}] : List VarN), b{k})"
    let obtainPat := if n == 0 then "rfl" else s!"⟨{", ".intercalate ws}, {", ".intercalate ((List.range n).map (s!"hw{·}"))}, rfl⟩"
    arms := arms.push s!"  | {c.componentsRev.head!} {" ".intercalate as} =>
    simp only [{T}.cakeInv] at hv
    obtain {obtainPat} := hv
    exact ⟨_, _, _, ([{", ".intercalate ws}] : List Value), by simp, rfl, rfl,
      h{k} {" ".intercalate as} rfl {" ".intercalate ws} {" ".intercalate ((List.range n).map (s!"hw{·}"))}⟩"
  let lookupArms := String.join ((List.range nC).map fun k => s!"\n      · exact {proj k}")
  let nodupArms := String.join ((List.range nC).map fun k => s!"\n      · exact hnd{k}")
  let rcasesPat := " | ".intercalate ((List.range nC).map fun _ => "⟨rfl, rfl, rfl⟩")
  runCmd s!"open ConPastel.Translator Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.NamespaceHOL in
theorem _root_.{T}.cake_mat {"{"}env : SemEnv Value{"}"} (hc : {T}.cakeHasCons env.c)
    {"{"}e : Exp{"}"} {"{"}x : {T}{"}"} (he : Eval env e ({T}.cakeInv x)) {"{"}Q : {T} → Value → Prop{"}"}
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
{"\n".intercalate arms.toList}"
  modifyEnv fun env => datatypeExt.addEntry env
    { name := T, stamp, ctors := ctors.map fun (c, tys) => (c, tys.size) }

elab "cake_datatype " id:ident : command => do
  let T ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  cakeDatatype T

end ConPastel.Translator.Meta
