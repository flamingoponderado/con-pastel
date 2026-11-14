import Lean
import ConPastel.Translator.Lemmas
import ConPastel.Translator.Tuple
import ConPastel.Translator.Meta.Core
import ConPastel.Translator.Meta.Ext
import ConPastel.Translator.Meta.Keys

/-!
# The proof-producing translator, goal-directed

The translator works backwards on goals `Eval env ?ce (INV t)`: it picks the
lemma for the head of the Lean term `t`, and the lemma's conclusion fixes the
CakeML expression `?ce` by unification. Binders are entered with fresh
locals, so the expression metavariables (created outside) never depend on
them.
-/

namespace ConPastel.Translator.Meta
open Lean Meta Elab
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

structure GLVar where
  fvar : Expr
  cname : String
  value : Expr
  rel : Expr

/-- The function whose body is being translated, when it is recursive. -/
structure RecFn where
  /-- Head constant of the Lean function. -/
  head : Name
  /-- Static (non-recursive) arguments it is applied to. -/
  static : Array Expr
  /-- The induction hypothesis: `∀ y, r y x → ∀ yv, A y yv → AppReturns cl yv (B (f y))`. -/
  ih : Expr
  /-- The recursive closure value and its CakeML name. -/
  cl : Expr
  cname : String
  /-- Number of curried arguments after the static ones; when more than one,
  the recursive closure takes them as a nested tuple. -/
  arity : Nat := 1
  /-- Well-founded functions translated from their functional: where each data
  argument comes from in `c._unary fixed ⟨packed…⟩` (`(true, k)`: fixed
  argument `k`; `(false, k)`: packed component `k`) and the number of packed
  components. -/
  argSrc : Array (Bool × Nat) := #[]
  nPacked : Nat := 0
  lvls : List Level := []
  /-- A dependent result type: the result invariant as a function of the
  argument tuple, and the tupled function. -/
  dep? : Option (Expr × Expr) := none

/-- A member of a mutual block being translated. -/
structure BlockMember where
  head : Name
  arity : Nat
  /-- The recursive closure value and its CakeML name. -/
  cl : Expr
  cname : String
  /-- The injection of the member's argument tuple into the block's sum type. -/
  inj : Expr
  /-- Argument and result invariants, and the tupled function. -/
  invT : Expr
  invB : Expr
  ft : Expr

/-- The mutual block being translated: the joint induction hypothesis
`∀ s', r s' s → Pred s'` at the current sum value `s`. -/
structure MutRec where
  members : Array BlockMember
  ih : Expr
  s : Expr
  r : Expr

structure GCtx where
  hbool : Expr
  /-- Proof of `HasListCons env.c`. -/
  hlist : Expr := default
  /-- For each registered datatype, a proof of `T.cakeHasCons env.c`. -/
  hasCons : NameMap Expr := {}
  globals : Std.HashMap Expr GlobalVar := {}
  globalLookup : Expr → String → MetaM Expr := fun _ n => throwError "no global {n}"
  rec? : Option RecFn := none
  /-- Unfold singleton recursive groups in lookups (the older commands). -/
  unfoldRec : Bool := true
  /-- Runtime-assumption replacements in scope: `(K, K', hypothesis)`. -/
  assumed : Array (Name × Name × Expr) := #[]
  /-- The mutual block being translated, if any. -/
  mrec? : Option MutRec := none

structure GSt where
  locals : Array GLVar := #[]
  fresh : Nat := 0

abbrev GoalM := StateRefT GSt (ReaderT GCtx MetaM)

/-- The translation needs the unit for `key` first. -/
def needUnitTag : String := "cake: need unit "

initialize needUnitRef : IO.Ref (Option Expr) ← IO.mkRef none

/-- Lean's own decreasing proof for the recursive call being translated. -/
initialize decHintRef : IO.Ref (Option Expr) ← IO.mkRef none

/-- The `n` components of a packed (`PSigma`) argument tuple. -/
partial def psigmaComps (e : Expr) (n : Nat) : Array Expr :=
  if n ≤ 1 then #[e] else
  match e.consumeMData.getAppFnArgs with
  | (``PSigma.mk, #[_, _, a, b]) => #[a] ++ psigmaComps b (n - 1)
  | _ => #[Expr.proj ``PSigma 0 e] ++ psigmaComps (Expr.proj ``PSigma 1 e) (n - 1)

def throwNeedUnit {α : Type} (key : Expr) : MetaM α := do
  needUnitRef.set (some key)
  throwError "{needUnitTag}{key}"

def getLevels (_args : Array Expr) : MetaM (List Level) := pure []

def freshCName (pfx : String := "v") : GoalM String := do
  let s ← get
  set { s with fresh := s.fresh + 1 }
  return s!"{pfx}{s.fresh}"

/-- The simp set for variable lookups. With `unfoldRec`, singleton
recursive groups are unfolded (`buildRecEnv`); otherwise lookups into the
recursive group come from hypotheses in context. -/
def lookupSimp (unfoldRec : Bool) : MetaM Syntax.Tactic :=
  if unfoldRec then
    `(tactic| simp (config := { decide := true }) only [*, nsLookup_nsBind_short, nsOptBind, ite_true,
      ite_false, SemEnv.v, recBodyEnv, buildRecEnv, List.foldr_cons, List.foldr_nil, clauseEnv,
      nsLookup_nsAppend_alist_short, List.zip_cons_cons, List.zip_nil_left, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.lookup, beq_eq_decide_of_decEq,
      decide_true, decide_false])
  else
    `(tactic| simp (config := { decide := true }) only [*, nsLookup_nsBind_short, nsOptBind, ite_true,
      ite_false, SemEnv.v, recBodyEnv, clauseEnv,
      nsLookup_nsAppend_alist_short, List.zip_cons_cons, List.zip_nil_left, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.lookup, beq_eq_decide_of_decEq,
      decide_true, decide_false])

def mlStringLit? (e : Expr) : Option String :=
  match e.consumeMData with
  | .app (.const ``Flapjack.Basis.Pure.MlString.ofString _) (.lit (.strVal s)) => some s
  | _ => none

partial def listLit? (e : Expr) : Option (List Expr) :=
  match e.consumeMData.getAppFnArgs with
  | (``List.nil, _) => some []
  | (``List.cons, #[_, a, rest]) => (listLit? rest).map (a :: ·)
  | _ => none

/-- A direct proof of `nsLookup ns (.short n) = some v`, following the shape
of the environments the translator builds. Returns `(v, proof)`. -/
partial def lookupNs (ns : Expr) (n : String) : MetaM (Expr × Expr) := do
  let ns ← instantiateMVars ns
  let nm := mlString n
  match ns.consumeMData.getAppFnArgs with
  | (``SemEnv.v, #[_, env]) =>
    match env.consumeMData.getAppFnArgs with
    | (``SemEnv.mk, #[_, a, _]) => lookupNs a n
    | (``recBodyEnv, #[envC, funs, p, xv]) =>
      lookupNs (← mkAppM ``nsBind #[p, xv, ← mkAppM ``buildRecEnv #[funs, envC, ← mkAppM ``SemEnv.v #[envC]]]) n
    | (``clauseEnv, #[env', xs, vs]) =>
      let some xl := listLit? xs | throwError "clause names not a literal"
      let some vl := listLit? vs | throwError "clause values not a literal"
      let pairs ← (xl.zip vl).reverse.mapM fun (x, v) => mkAppM ``Prod.mk #[x, v]
      let pty ← mkAppM ``Prod #[mkConst ``VarN, mkConst ``Value]
      let al ← mkListLit pty pairs
      lookupNs (← mkAppM ``nsAppend #[← mkAppOptM ``alistToNs #[mkConst ``ModN, none, none, al],
        ← mkAppM ``SemEnv.v #[env']]) n
    | _ => throwError "lookup: opaque environment {env}"
  | (``nsBind, #[_, _, _, k, x, rest]) => lookBind k x rest
  | (``nsOptBind, #[_, _, _, o, x, rest]) =>
    match o.consumeMData.getAppFnArgs with
    | (``Option.some, #[_, k]) => lookBind k x rest
    | _ => lookupNs rest n
  | (``nsAppend, #[_, _, _, a, rest]) =>
    match a.consumeMData.getAppFnArgs with
    | (``alistToNs, #[_, _, _, al]) =>
      let some l := listLit? al | throwError "alist not a literal"
      match l with
      | [] =>
        let (v, h) ← lookupNs rest n
        return (v, ← mkAppM ``lk_app_nil #[rest, nm, h])
      | p :: tl =>
        let (``Prod.mk, #[_, _, k, x]) := p.consumeMData.getAppFnArgs | throwError "alist entry"
        let some ks := mlStringLit? k | throwError "alist key not a literal"
        let tlE ← mkListLit (← inferType p) tl
        if ks == n then return (x, ← mkAppM ``lk_app_same #[k, x, tlE, rest])
        let (v, h) ← lookupNs (← mkAppM ``nsAppend #[← mkAppOptM ``alistToNs #[mkConst ``ModN, none, none, tlE], rest]) n
        let hne ← mkDecideProof (mkNot (← mkEq nm k))
        return (v, ← mkAppM ``lk_app_ne #[hne, x, tlE, rest, h])
    | _ => throwError "lookup: nsAppend of {a}"
  | (``buildRecEnv, _) =>
    -- a lookup hypothesis about the recursive group
    let lctx ← getLCtx
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if let some (_, lhs, rhs) := ty.eq? then
        if let (``nsLookup, #[_, _, _, _, _, ns', idt]) := lhs.getAppFnArgs then
          if let (``Ident.short, #[_, _, k]) := idt.getAppFnArgs then
            if mlStringLit? k == some n && (← isDefEq ns' ns) then
              if let (``Option.some, #[_, v]) := rhs.getAppFnArgs then
                return (v, d.toExpr)
    throwError "lookup: no hypothesis for {n} in the recursive group"
  | _ => throwError "lookup: unsupported namespace {ns}"
where
  lookBind (k x rest : Expr) : MetaM (Expr × Expr) := do
    let some ks := mlStringLit? k | throwError "bound name not a literal"
    if ks == n then return (x, ← mkAppM ``lk_bind_same #[k, x, rest])
    let (v, h) ← lookupNs rest n
    let hne ← mkDecideProof (mkNot (← mkEq (mlString n) k))
    return (v, ← mkAppM ``lk_bind_ne #[hne, x, rest, h])

def proveLookupG (env : Expr) (n : String) (v : Expr) (unfoldRec : Bool := true) : MetaM Expr := do
  -- direct proof first
  let direct? ← try
      let (v', pf) ← lookupNs (← mkAppM ``SemEnv.v #[env]) n
      if ← isDefEq v' v then pure (some pf) else
        if (← IO.getEnv "CAKE_TRACE").isSome then cakeLog s!"[lookup-fallback] {n}: value mismatch"
        pure none
    catch e =>
      if (← IO.getEnv "CAKE_TRACE").isSome then
        cakeLog s!"[lookup-fallback] {n}: {(← e.toMessageData.toString).take 300}"
      pure none
  if let some pf := direct? then return pf
  let goal ← mkEq (← mkAppM ``nsLookup #[← mkAppM ``SemEnv.v #[env], shortIdent n])
    (← mkAppM ``Option.some #[v])
  let mvar ← mkFreshExprMVar goal
  let remaining ← try
      Tactic.run mvar.mvarId! (Tactic.evalTactic (← lookupSimp unfoldRec)) |>.run'
    catch e => throwError "lookup of {n} failed: {e.toMessageData}\ngoal: {goal}"
  unless remaining.isEmpty do
    throwError "lookup of {n} not proved"
  instantiateMVars mvar

/-- Run a tactic to close a side goal. -/
def closeWith (goal : Expr) (tac : Syntax.Tactic) : MetaM Expr := do
  if (← IO.getEnv "CAKE_DEBUG_LOCAL").isSome then
    let nm := Name.mkSimple ((← IO.getEnv "CAKE_DEBUG_LOCAL").getD "")
    for fv in (collectFVars {} (← instantiateMVars goal)).fvarIds do
      if let some d := (← getLCtx).find? fv then
        if d.userName == nm then cakeLog s!"[closeWith mentions {nm}] {← ppExpr goal} BY {tac}"
  let mvar ← mkFreshExprMVar goal
  let remaining ← Tactic.run mvar.mvarId! (Tactic.evalTactic tac) |>.run'
  unless remaining.isEmpty do
    throwError "side goal not closed: {goal}"
  instantiateMVars mvar

/-- Destructure a goal `Eval env ce P` into `(env, P)`. -/
def evalGoalParts (g : MVarId) : MetaM (Expr × Expr) := do
  let ty ← instantiateMVars (← g.getType)
  let ty := ty.headBeta
  match ty.getAppFnArgs with
  | (``Eval, #[env, _, p]) => return (env, p)
  | _ => throwError "not an Eval goal: {ty}"

def evalGoalCe (g : MVarId) : MetaM Expr := do
  let ty := (← instantiateMVars (← g.getType)).headBeta
  match ty.getAppFnArgs with
  | (``Eval, #[_, ce, _]) => return ce
  | _ => throwError "not an Eval goal: {ty}"

/-- A fresh goal `Eval env ?ce P`. -/
def newEvalGoal (env p : Expr) : MetaM (Expr × MVarId) := do
  let ce ← mkFreshExprMVar (mkConst ``Exp)
  let g ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, p])
  return (ce, g.mvarId!)

/-- Close `g` with the proof `pf`, unifying types (this fixes `?ce`). -/
def assignProof (g : MVarId) (pf : Expr) : MetaM Unit := do
  let pty ← inferType pf
  -- matchers (`instance_reducible`) only unfold at transparency `.all`
  unless (← isDefEq pty (← g.getType)) || (← withTransparency .all (isDefEq pty (← g.getType))) do
    throwError "lemma does not fit goal:\n{pty}\nvs\n{← g.getType}"
  if (← IO.getEnv "CAKE_TRACE").isSome then
    let lctx ← getLCtx
    let pfI ← instantiateMVars pf
    for fv in (collectFVars {} pfI).fvarIds do
      unless lctx.contains fv do
        throwError "proof uses a local not in scope ({mkFVar fv}) for goal {← g.getType}"
  g.assign pf

/-- `B (f a)` with `B` and the Lean term split out of `P`. -/
def splitInv (p : Expr) : MetaM (Expr × Expr) := do
  let p ← instantiateMVars p
  match p with
  | .app inv t => return (inv, t)
  | _ => throwError "invariant application expected: {p}"

/-- `t` with the occurrences of the discriminant `d` abstracted (`d` need not
be a free variable); fails rather than produce a `let` that changes nothing. -/
def abstractDiscr (t d : Expr) : MetaM Expr := do
  let b ← kabstract t d
  unless b.hasLooseBVars do throwError "cannot abstract discriminant {d} in {t}"
  return b

/-- Does the local `x` occur inside a proof or a type in `e`? (Then `e` may
only typecheck with `x`'s definition unfolded.) -/
partial def occursInProofOrType (e : Expr) (x : FVarId) : MetaM Bool := do
  if !e.containsFVar x then return false
  if e.isFVar then return false
  if (← isProof e) || (← isType e) then return true
  match e with
  | .app .. =>
    -- a proof argument's expected type may mention `x` (through other arguments)
    let args := e.getAppArgs
    for a in args do
      if ← isProof a then return true
    if ← occursInProofOrType e.getAppFn x then return true
    for a in args do
      if ← occursInProofOrType a x then return true
    return false
  | .lam n t b bi | .forallE n t b bi =>
    if t.containsFVar x then return true
    withLocalDecl n bi t fun y => occursInProofOrType (b.instantiate1 y) x
  | .letE n t v b _ =>
    if t.containsFVar x then return true
    if ← occursInProofOrType v x then return true
    withLocalDeclD n t fun y => occursInProofOrType (b.instantiate1 y) x
  | .mdata _ b => occursInProofOrType b x
  | .proj _ _ b => occursInProofOrType b x
  | _ => return false

/-- `let z := d; t[z]`'s body: the discriminant replaced at its argument
position `pos` only when that keeps the application type-correct (shallow
check), else all occurrences of `d` (e.g. alternatives' binder types). -/
def discrLetBody (t d : Expr) (pos : Nat) : MetaM Expr := do
  let args := t.getAppArgs
  let positional := mkAppN t.getAppFn (args.set! pos (.bvar 0))
  let ok ← withLocalDeclD `z (← inferType d) fun z => do
    let e := positional.instantiate1 z
    let mut fty ← inferType e.getAppFn
    for a in e.getAppArgs do
      let .forallE _ dom b _ ← whnf fty | return false
      unless ← isDefEq (← inferType a) dom do return false
      fty := b.instantiate1 a
    return true
  if ok then return positional
  abstractDiscr t d

/-- A value of type `ty`, for defaults that are never used at runtime (total
versions of bounded accessors): an `Inhabited` instance, else a constructor
with defaulted fields. -/
partial def defaultOf? (ty : Expr) (fuel : Nat := 6) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  if let .some inh ← trySynthInstance (← mkAppM ``Inhabited #[ty]) then
    return some (← mkAppOptM ``Inhabited.default #[ty, inh])
  let ty ← whnfR ty
  let .const I us := ty.getAppFn | return none
  let some (.inductInfo ii) := (← getEnv).find? I | return none
  if ← isProp ty then return none
  let params := ty.getAppArgs[:ii.numParams].toArray
  for c in ii.ctors do
    let ci ← getConstInfo c
    let mut cty ← instantiateForall (← instantiateTypeLevelParams ci.toConstantVal us) params
    let mut args : Array Expr := #[]
    let mut ok := true
    while true do
      let cty' ← whnf cty
      let .forallE _ dom _ _ := cty' | break
      if ← isProp dom then ok := false; break
      if dom.getAppFn.isConstOf I then ok := false; break
      let some v ← defaultOf? dom (fuel - 1) | ok := false; break
      args := args.push v
      cty := cty'.bindingBody!.instantiate1 v
    if ok then return some (mkAppN (mkConst c us) (params ++ args))
  return none

mutual

partial def solve (g : MVarId) : GoalM Unit := do
  let trace := (← IO.getEnv "CAKE_TRACE").isSome
  let t0 ← IO.monoMsNow
  if trace then
    let (_, p) ← evalGoalParts g
    cakeLog s!"[enter] {((← ppExpr p).pretty.replace "\n" " ").take 1500}"
  try
    solveCore g
    if trace then
      let dt := (← IO.monoMsNow) - t0
      if dt > 1000 then
        let (_, p) ← evalGoalParts g
        cakeLog s!"[trace] {dt}ms {(← ppExpr p).pretty.take 300}"
  catch e =>
    let msg ← e.toMessageData.toString
    if (msg.splitOn needUnitTag).length > 1 || (msg.splitOn "[in ").length > 1 ||
        (msg.splitOn "cake: need datatype").length > 1 then throw e
    let (_, p) ← evalGoalParts g
    throwError "{e.toMessageData} [in {p}]"

partial def solveCore (g : MVarId) : GoalM Unit := do
  let (env, p) ← evalGoalParts g
  let (inv, t) ← splitInv p
  let t := (← instantiateMVars t).headBeta
  -- a beta-redex whose head lambda is wrapped in metadata
  let t := if t.getAppFn.consumeMData.isLambda && t.getAppNumArgs > 0 then
      (mkAppN t.getAppFn.consumeMData t.getAppArgs).headBeta else t
  -- `(let x := v; b) a…` is `let x := v; b a…`
  if let .letE n ty v b nd := t.getAppFn.consumeMData then
    if t.getAppNumArgs > 0 then
      let t' := Expr.letE n ty v (mkAppN b (t.getAppArgs.map (·.liftLooseBVars 0 1))) nd
      return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t']))
  let st ← get
  let ctx ← read
  -- locals
  if t.isFVar then
    let some lv := st.locals.find? (·.fvar == t) | throwError "unknown local {t}"
    let hl ← proveLookupG env lv.cname lv.value ctx.unfoldRec
    assignProof g (← mkAppOptM ``Eval_var #[env, shortIdent lv.cname, lv.value, p, hl, lv.rel])
    return
  -- `decide (b = true)` is `b` (avoids unfolding the `Bool` decidable-equality instance)
  if inv.isConstOf ``BOOL then
    if let (``Decidable.decide, #[prop, dinst]) := t.getAppFnArgs then
      if let some (ty, b, tr) := prop.eq? then
        if ty.isConstOf ``Bool && tr.isConstOf ``Bool.true then
          let ce ← evalGoalCe g
          let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv b])
          solve gb.mvarId!
          let heq ← mkEqSymm (← mkAppOptM ``Bool.decide_eq_true #[b, dinst])
          let motive ← withLocalDeclD `x (mkConst ``Bool) fun x => do
            mkLambdaFVars #[x] (← mkAppM ``Eval #[env, ce, mkApp inv x])
          let pf ← mkEqMP (← mkCongrArg motive heq) (← instantiateMVars gb)
          g.assign pf
          return
  -- `List.get l f` (dependent on `l`) as `List.getD l f.val default` for inhabited types
  if let (``List.get, #[α, l, f]) := t.getAppFnArgs then
    if let some dflt ← defaultOf? α then
      let heq ← mkAppOptM ``list_get_eq_getD' #[α, l, f, dflt]
      let t' ← mkAppOptM ``List.getD #[α, l, ← mkAppM ``Fin.val #[f], dflt]
      let ce ← evalGoalCe g
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv t'])
      solve gb.mvarId!
      let motive ← withLocalDeclD `x α fun x => do mkLambdaFVars #[x] (← mkAppM ``Eval #[env, ce, mkApp inv x])
      g.assign (← mkEqMP (← mkCongrArg motive (← mkEqSymm heq)) (← instantiateMVars gb))
      return
  -- `Option.get o h` as `Option.getD o default` for inhabited types
  if let (``Option.get, #[α, o, h]) := t.getAppFnArgs then
    if let some dflt ← defaultOf? α then
      let heq ← mkAppOptM ``option_get_eq_getD' #[α, o, h, dflt]
      let t' ← mkAppOptM ``Option.getD #[α, o, dflt]
      let ce ← evalGoalCe g
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv t'])
      solve gb.mvarId!
      let motive ← withLocalDeclD `x α fun x => do mkLambdaFVars #[x] (← mkAppM ``Eval #[env, ce, mkApp inv x])
      g.assign (← mkEqMP (← mkCongrArg motive (← mkEqSymm heq)) (← instantiateMVars gb))
      return
  -- `for x in l` loops: `List.forIn' l init (fun a _ b => body)` (membership proof unused)
  -- as the structural `listForIn` (`List.forIn'.loop` carries the proofs)
  if let (``List.forIn', #[α, β, m, minst, l, init, f]) := t.getAppFnArgs then
    let f'? ← withLocalDeclD `a α fun a => do
      let .forallE _ hty _ _ ← whnf (← inferType (mkApp f a)) | return none
      withLocalDeclD `h hty fun h => withLocalDeclD `b β fun b => do
        let e ← Meta.transform (mkApp3 f a h b).headBeta (pre := fun x => pure (.continue x.headBeta))
        if e.containsFVar h.fvarId! then return none
        return some (← mkLambdaFVars #[a, b] e)
    if let some f' := f'? then
        let heq ← mkAppOptM ``ConPastel.Impl.forIn'_eq_listForIn #[m, minst, none, none, l, init, f']
        let t' := (← inferType heq).appArg!
        let ce ← evalGoalCe g
        let R ← inferType t
        let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv t'])
        solve gb.mvarId!
        let motive ← withLocalDeclD `w R fun w => do mkLambdaFVars #[w] (← mkAppM ``Eval #[env, ce, mkApp inv w])
        let pf ← mkEqMP (← mkCongrArg motive (← mkEqSymm heq)) (← instantiateMVars gb)
        let g ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ce, mkApp inv (← inferType heq).appFn!.appArg!])
        g.assign pf
        return
  -- `for i in [a:b:s]` loops (membership proof unused): `listForIn` over `List.range'`
  if let (``Std.Legacy.Range.forIn', #[m, β, minst, rg, init, f]) := t.getAppFnArgs then
    let f'? ← withLocalDeclD `a (mkConst ``Nat) fun a => do
      let .forallE _ hty _ _ ← whnf (← inferType (mkApp f a)) | return none
      withLocalDeclD `h hty fun h => withLocalDeclD `b β fun b => do
        let e ← Meta.transform (mkApp3 f a h b).headBeta (pre := fun x => pure (.continue x.headBeta))
        if e.containsFVar h.fvarId! then return none
        return some (← mkLambdaFVars #[a, b] e)
    if let some f' := f'? then
      let heq ← mkAppOptM ``ConPastel.Impl.rangeForIn'_eq #[m, minst, β, rg, init, f']
      let t' := (← inferType heq).appArg!
      let ce ← evalGoalCe g
      let R ← inferType t
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv t'])
      solve gb.mvarId!
      let motive ← withLocalDeclD `w R fun w => do mkLambdaFVars #[w] (← mkAppM ``Eval #[env, ce, mkApp inv w])
      let pf ← mkEqMP (← mkCongrArg motive (← mkEqSymm heq)) (← instantiateMVars gb)
      let g ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ce, mkApp inv (← inferType heq).appFn!.appArg!])
      g.assign pf
      return
  -- string literals: `s` is `String.ofByteArray ⟨⟨[bytes]⟩⟩ s.isValidUTF8` (structure eta)
  if let .lit (.strVal str) := t then
    let u8 := mkConst ``UInt8
    let bytes ← str.toUTF8.toList.mapM fun b => mkNumeral u8 b.toNat
    let arr ← mkAppOptM ``Array.mk #[u8, ← mkListLit u8 bytes]
    let ba := mkApp (mkConst ``ByteArray.mk) arr
    let t' := mkApp2 (mkConst ``String.ofByteArray) ba (mkApp (mkConst ``String.isValidUTF8) t)
    let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
    return ← solve g'
  -- literals
  if let some n := t.nat? then
    if inv.isConstOf ``NAT then
      assignProof g (← mkAppM ``Eval_nat_lit #[env, toExpr n])
      return
  if let some n := t.rawNatLit? then
    assignProof g (← mkAppM ``Eval_nat_lit #[env, toExpr n])
    return
  if t.isConstOf ``Bool.true || t.isConstOf ``Bool.false then
    assignProof g (← mkAppOptM ``Eval_bool_lit #[env, ctx.hbool, toExpr (t.isConstOf ``Bool.true)])
    return
  match t with
  | .proj I j sExp =>
    if let some v ← Meta.projectCore? sExp.consumeMData j then
      return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv v]))
    if let some (I', j', _) ← newtypeInfo? (← inferType sExp) then
      if I' == I && j' == j then
        let invS ← invOf (← inferType sExp)
        let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp invS sExp])
        return ← solve g'
    if I == ``Prod then
      -- `case s of (x, y) => x` (or `y`)
      let sty ← whnfD (← inferType sExp)
      let (``Prod, #[aty, bty]) := sty.getAppFnArgs | throwError "bad pair projection {t}"
      let invP ← invOf sty
      let (``PAIR, #[_, _, invA, invB]) := invP.getAppFnArgs | throwError "bad pair invariant"
      let (_, gs) ← newEvalGoal env (mkApp invP sExp)
      solve gs
      let xn ← freshCName "t"
      let yn ← freshCName "t"
      let hxy ← closeWith (mkNot (← mkEq (mlString xn) (mlString yn))) (← `(tactic| decide))
      let invC := if j == 0 then invA else invB
      let f ← withLocalDeclD `a aty fun a => withLocalDeclD `b bty fun b => mkLambdaFVars #[a, b] (if j == 0 then a else b)
      let picked := if j == 0 then xn else yn
      let body := mkApp (mkConst ``Exp.var) (shortIdent picked)
      let hb ← withLocalDeclD `a aty fun a => withLocalDeclD `b bty fun b => do
        withLocalDeclD `heq (← mkEq sExp (← mkAppM ``Prod.mk #[a, b])) fun heq => do
        withLocalDeclD `av (mkConst ``Value) fun av => withLocalDeclD `bv (mkConst ``Value) fun bv => do
        withLocalDeclD `hav (mkApp2 invA a av) fun hav => withLocalDeclD `hbv (mkApp2 invB b bv) fun hbv => do
          let env' ← mkAppM ``clauseEnv #[env, ← mkListLit (mkConst ``VarN) [mlString xn, mlString yn],
            ← mkListLit (mkConst ``Value) [av, bv]]
          let (vj, hj) := if j == 0 then (av, hav) else (bv, hbv)
          let hl ← proveLookupG env' picked vj (← read).unfoldRec
          let pf ← mkAppOptM ``Eval_var #[env', shortIdent picked, vj, mkApp invC (if j == 0 then a else b), hl, hj]
          mkLambdaFVars #[a, b, heq, av, bv, hav, hbv] pf
      assignProof g (← mkAppOptM ``Eval_mat_pair #[aty, bty, none, invA, invB, invC, env, none, body,
        mlString xn, mlString yn, sExp, f, hxy, ← instantiateMVars (mkMVar gs), hb])
      return
    -- a field of a single-constructor datatype: `I.casesOn s (fun fs => f_j)` (structure eta)
    if let some (.inductInfo ii) := (← getEnv).find? I then
      if ii.ctors.length == 1 then
        let sty ← whnfD (← inferType sExp)
        -- the structure must be a registered datatype (else `casesOn` would be undone by structure eta)
        let _ ← invOf sty
        let .const _ lvls := sty.getAppFn | throwError "bad projection {t}"
        let params := sty.getAppArgs
        let R ← inferType t
        let cty ← instantiateForall (← instantiateTypeLevelParams (← getConstInfo ii.ctors.head!).toConstantVal lvls) params
        let alt ← forallTelescope cty fun fs _ => mkLambdaFVars fs fs[j]!
        let motive ← withLocalDeclD `x sty fun x => mkLambdaFVars #[x] R
        let uR ← getLevel R
        let t' := mkAppN (mkConst (I ++ `casesOn) (uR :: lvls)) (params ++ #[motive, sExp, alt])
        let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
        return ← solve g'
    throwError "unsupported projection {t}"
  | .letE n ty v b _ => solveLet g env inv n ty v b
  | .lam n ty b _ => solveLam g env inv n ty b
  | .mdata _ t' => solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, (← evalGoalCe g), mkApp inv t']))
  | _ => solveApp g env inv t

partial def solveLet (g : MVarId) (env inv : Expr) (n : Name) (ty v b : Expr) : GoalM Unit := do
  -- lets of propositions, proofs and types have no runtime content: substitute
  if (← isProp ty) || (← whnfD ty).isSort then
    let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv (b.instantiate1 v)])
    return ← solve g'
  -- a body that only typechecks with the definition unfolded (proofs about the
  -- bound value, e.g. Lean's own decreasing proofs): substitute
  -- (the solver's own discriminant lets `z` are built to typecheck opaquely)
  let opaqueOk ← if n == `z then pure true else withLocalDeclD n ty fun x => do
    return !(← occursInProofOrType (b.instantiate1 x) x.fvarId!)
  unless opaqueOk do
    let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv (b.instantiate1 v)])
    return ← solve g'
  let cname ← freshCName
  let invV ← invOf ty
  let (_, gv) ← newEvalGoal env (mkApp invV v)
  solve gv
  let ceB ← mkFreshExprMVar (mkConst ``Exp)
  let pfB ← withLocalDeclD n ty fun x => do
    withLocalDeclD `heq (← mkEq x v) fun heq => do
    withLocalDeclD `xv (mkConst ``Value) fun xv => do
    withLocalDeclD `hx (mkApp2 invV x xv) fun hx => do
      let env' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsBind #[mlString cname, xv, ← mkAppM ``SemEnv.v #[env]],
        ← mkAppM ``SemEnv.c #[env]]
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env', ceB, mkApp inv (b.instantiate1 x)])
      modify fun s => { s with locals := s.locals.push { fvar := x, cname, value := xv, rel := hx } }
      solve gb.mvarId!
      modify fun s => { s with locals := s.locals.pop }
      mkLambdaFVars #[x, heq, xv, hx] (← instantiateMVars gb)
  let bfun ← withLocalDeclD n ty fun x => mkLambdaFVars #[x] (b.instantiate1 x)
  let pf ← mkAppOptM ``Eval_let_eq #[none, none, invV, inv, env, mlString cname, none, ceB, v, bfun,
    ← instantiateMVars (mkMVar gv), pfB]
  assignProof g pf

partial def solveLam (g : MVarId) (env inv : Expr) (n : Name) (ty b : Expr) : GoalM Unit := do
  let cname ← freshCName
  -- inv must be `Arrow A B`
  let inv ← whnfR inv
  if let (``DARROWP, #[_, _, _, invA, invB]) := inv.getAppFnArgs then
    -- the proof binder (eta-expand a body that is a function of the proof)
    let b ← if b.isLambda then pure b else do
      let .forallE _ pty _ _ ← whnf (← withLocalDeclD n ty fun x => do inferType (b.instantiate1 x))
        | throwError "expected a function over a proof: {b}"
      pure (Expr.lam `h pty (mkApp (b.liftLooseBVars 0 1) (.bvar 0)) .default)
    let .lam hn p body' _ := b | throwError "expected a lambda over a proof"
    let ceB ← mkFreshExprMVar (mkConst ``Exp)
    let h ← withLocalDeclD n ty fun x => do
      withLocalDeclD `xv (mkConst ``Value) fun xv => do
      withLocalDeclD `hx (mkApp2 invA x xv) fun hx => do
      withLocalDeclD hn (p.instantiate1 x) fun hp => do
        let env' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsBind #[mlString cname, xv, ← mkAppM ``SemEnv.v #[env]],
          ← mkAppM ``SemEnv.c #[env]]
        let bodyT := (body'.instantiate1 hp).instantiate1 x
        let _ := bodyT
        let bodyT := (b.instantiate1 x).bindingBody!.instantiate1 hp
        let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env', ceB, mkApp (invB.beta #[x, hp]) bodyT])
        modify fun s => { s with locals := s.locals.push { fvar := x, cname, value := xv, rel := hx } }
        solve gb.mvarId!
        modify fun s => { s with locals := s.locals.pop }
        mkLambdaFVars #[x, xv, hx, hp] (← instantiateMVars gb)
    let f ← withLocalDeclD n ty fun x => mkLambdaFVars #[x] (b.instantiate1 x)
    assignProof g (← mkAppOptM ``Eval_fn_darrowp #[none, none, none, invA, invB, env, mlString cname, ceB, f, h])
    return
  if let (``DARROW, #[_, _, invA, invB]) := inv.getAppFnArgs then
    let ceB ← mkFreshExprMVar (mkConst ``Exp)
    let h ← withLocalDeclD n ty fun x => do
      withLocalDeclD `xv (mkConst ``Value) fun xv => do
      withLocalDeclD `hx (mkApp2 invA x xv) fun hx => do
        let env' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsBind #[mlString cname, xv, ← mkAppM ``SemEnv.v #[env]],
          ← mkAppM ``SemEnv.c #[env]]
        let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env', ceB, mkApp (invB.beta #[x]) (b.instantiate1 x)])
        modify fun s => { s with locals := s.locals.push { fvar := x, cname, value := xv, rel := hx } }
        solve gb.mvarId!
        modify fun s => { s with locals := s.locals.pop }
        mkLambdaFVars #[x, xv, hx] (← instantiateMVars gb)
    let f ← withLocalDeclD n ty fun x => mkLambdaFVars #[x] (b.instantiate1 x)
    assignProof g (← mkAppOptM ``Eval_fn_darrow #[none, none, invA, invB, env, mlString cname, ceB, f, h])
    return
  let (``Arrow, #[_, _, invA, invB]) := inv.getAppFnArgs
    | throwError "function expected to have an Arrow invariant, got {inv}"
  let ceB ← mkFreshExprMVar (mkConst ``Exp)
  let h ← withLocalDeclD n ty fun x => do
    withLocalDeclD `xv (mkConst ``Value) fun xv => do
    withLocalDeclD `hx (mkApp2 invA x xv) fun hx => do
      let env' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsBind #[mlString cname, xv, ← mkAppM ``SemEnv.v #[env]],
        ← mkAppM ``SemEnv.c #[env]]
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env', ceB, mkApp invB (b.instantiate1 x)])
      modify fun s => { s with locals := s.locals.push { fvar := x, cname, value := xv, rel := hx } }
      solve gb.mvarId!
      modify fun s => { s with locals := s.locals.pop }
      mkLambdaFVars #[x, xv, hx] (← instantiateMVars gb)
  let f ← withLocalDeclD n ty fun x => mkLambdaFVars #[x] (b.instantiate1 x)
  assignProof g (← mkAppOptM ``Eval_fn_arrow #[none, none, invA, invB, env, mlString cname, ceB, f, h])

/-- Translate `decide c`: a goal `Eval env ?ce (BOOL (decide c))`. -/
partial def solveDecide (g : MVarId) (env c : Expr) : GoalM Unit := do
  let c ← whnfR c
  let binNat (lem : Name) (a b : Expr) : GoalM Unit := do
    let (_, ga) ← newEvalGoal env (mkApp (mkConst ``NAT) a)
    let (_, gb) ← newEvalGoal env (mkApp (mkConst ``NAT) b)
    solve ga; solve gb
    assignProof g (← mkAppM lem #[← instantiateMVars (mkMVar ga), ← instantiateMVars (mkMVar gb)])
  match c.getAppFnArgs with
  | (``LT.lt, #[ty, _, a, b]) => if (← whnfR ty).isConstOf ``Nat then return ← binNat ``Eval_nat_lt a b
  | (``LE.le, #[ty, _, a, b]) => if (← whnfR ty).isConstOf ``Nat then return ← binNat ``Eval_nat_le a b
  | (``Eq, #[ty, a, b]) => if (← whnfR ty).isConstOf ``Nat then return ← binNat ``Eval_nat_eq a b
  | _ => pure ()
  -- any other instance: `decide c` is the projection of the instance (a newtype)
  let t ← mkAppOptM ``Decidable.decide #[c, none]
  let _ := t
  throwError "unsupported condition {c}"

/-- Split on the `Decidable P` argument at position `pos` of `t`:
`t[d] = dite P (fun h => t[isTrue h]) (fun h => t[isFalse h])` (by cases on
`d`), after which the branches reduce. Returns whether it applied. -/
partial def solveDecSplit (g : MVarId) (env inv t : Expr) (pos : Nat) : GoalM Bool := do
  let args := t.getAppArgs
  let d := args[pos]!
  let (``Decidable, #[P]) := (← whnfR (← inferType d)).getAppFnArgs | return false
  if d.getAppFn.isConstOf ``Decidable.isTrue || d.getAppFn.isConstOf ``Decidable.isFalse ||
      d.getAppFn.isConstOf ``Decidable.intro then return false
  let R ← inferType t
  let tAt (x : Expr) : Expr := mkAppN t.getAppFn (args.set! pos x)
  let a ← withLocalDeclD `h P fun h => do mkLambdaFVars #[h] (tAt (← mkAppOptM ``Decidable.isTrue #[P, h]))
  let b ← withLocalDeclD `h (mkNot P) fun h => do mkLambdaFVars #[h] (tAt (← mkAppOptM ``Decidable.isFalse #[P, h]))
  let eqTy ← withLocalDeclD `x (← inferType d) fun x => do
    mkForallFVars #[x] (← mkEq (tAt x) (← mkAppOptM ``dite #[R, P, x, a, b]))
  let eqAll? ← try some <$> closeWith eqTy (← `(tactic| (intro x; rcases x with ⟨b, r⟩; cases b <;> with_unfolding_all rfl)))
    catch _ => pure none
  let some eqAll := eqAll? | return false
  let heq := mkApp eqAll d
  let t' ← mkAppOptM ``dite #[R, P, d, a, b]
  let ce ← evalGoalCe g
  let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv t'])
  solve gb.mvarId!
  let motive ← withLocalDeclD `w R fun w => do mkLambdaFVars #[w] (← mkAppM ``Eval #[env, ce, mkApp inv w])
  g.assign (← mkEqMP (← mkCongrArg motive (← mkEqSymm heq)) (← instantiateMVars gb))
  return true

/-- A `casesOn` with a dependent motive whose result is a newtype (e.g.
`Decidable (x = b)`): the projection commutes with the case split,
`(casesOn x alts).1 = casesOn x (fun fs => (alt fs).1)` (proved by cases). -/
partial def solveDepCasesNewtype (g : MVarId) (env inv fn : Expr) (np : Nat) (args : Array Expr) (τ : Expr) :
    GoalM Unit := do
  let major := args[np + 1]!
  let alts := args[np + 2:].toArray
  let (``NEWTYPE, #[_, F, proj, A]) := inv.getAppFnArgs
    | throwError "dependent casesOn motive not supported (invariant {inv})"
  unless major.isFVar do throwError "dependent casesOn on a non-variable {major}"
  let .const cn lvls := fn | throwError "bad casesOn {fn}"
  let u ← getLevel F
  let motive' ← withLocalDeclD `x τ fun x => mkLambdaFVars #[x] F
  let alts' ← alts.mapM fun alt => do
    forallTelescope (← inferType alt) fun fs _ => do mkLambdaFVars fs (mkApp proj (mkAppN alt fs)).headBeta
  let t := mkAppN fn args
  let t' := mkAppN (mkConst cn (u :: lvls.tail!)) (args[:np].toArray ++ #[motive', major] ++ alts')
  let mv ← mkFreshExprMVar (← mkEq (mkApp proj t).headBeta t')
  let subs ← mv.mvarId!.cases major.fvarId!
  for sg in subs do sg.mvarId.refl
  let heq ← instantiateMVars mv
  let ce ← evalGoalCe g
  let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp A t'])
  solve gb.mvarId!
  let motiveE ← withLocalDeclD `w F fun w => do mkLambdaFVars #[w] (← mkAppM ``Eval #[env, ce, mkApp A w])
  let pf ← mkEqMP (← mkCongrArg motiveE (← mkEqSymm heq)) (← instantiateMVars gb)
  let g ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ce, mkApp A (mkApp proj t).headBeta])
  g.assign pf

partial def solveCases (g : MVarId) (env inv : Expr) (d : DatatypeInfo) (fn : Expr) (np : Nat)
    (args : Array Expr) : GoalM Unit := do
  let ctx ← read
  let motive := args[np]!
  let major := args[np + 1]!
  let alts := args[np + 2:].toArray
  let τ := d.ty
  let dep ← withLocalDeclD `x τ fun x => do
    return (← instantiateMVars (motive.beta #[x])).headBeta.containsFVar x.fvarId!
  if dep then return ← solveDepCasesNewtype g env inv fn np args τ
  unless major.isFVar do
    let letT := Expr.letE `z τ major (mkAppN fn (args[:np].toArray ++ #[motive, .bvar 0] ++ alts)) false
    let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv letT])
    return ← solve g'
  let st ← get
  let some lv := st.locals.find? (·.fvar == major) | throwError "unknown scrutinee {major}"
  let some hc := ctx.hasCons.find? d.name | throwError "no constructor environment for {τ}"
  let invT := mkConst (d.name ++ `cakeInv)
  let hl ← proveLookupG env lv.cname lv.value ctx.unfoldRec
  let he ← mkAppOptM ``Eval_var #[env, shortIdent lv.cname, lv.value, mkApp invT major, hl, lv.rel]
  let qfun ← withLocalDeclD `x τ fun x => do
    mkLambdaFVars #[x] (mkApp inv (mkAppN fn (args[:np].toArray ++ #[motive, x] ++ alts)))
  let mut lemArgs : Array (Option Expr) := #[some env, some hc, none, some major, some he, some qfun]
  let params := τ.getAppArgs
  let .const _ lvls := τ.getAppFn | unreachable!
  for k in [0:d.ctors.size] do
    let (c, _, dataFlags) := d.ctors[k]!
    let cty ← instantiateForall (← instantiateTypeLevelParams (← getConstInfo c).toConstantVal lvls) params
    let names ← (dataFlags.toList.filter id).mapM fun _ => freshCName "f"
    let nameList ← mkListLit (mkConst ``VarN) (names.map mlString)
    let hnd ← closeWith (← mkAppM ``List.Nodup #[nameList]) (← `(tactic| decide))
    let bk ← mkFreshExprMVar (mkConst ``Exp)
    let hk ← forallTelescope cty fun as _ => do
      let ctorApp := mkAppN (mkAppN (mkConst c lvls) params) as
      withLocalDeclD `heq (← mkEq major ctorApp) fun heq => do
      let dataAs := (as.toList.zip dataFlags.toList).filterMap fun (a, b) => if b then some a else none
      withLocalDeclsDND (dataAs.toArray.mapIdx fun i _ => (Name.mkSimple s!"w{i}", mkConst ``Value)) fun ws => do
      let invs ← dataAs.toArray.mapM fun a => do (invOf (← inferType a) : MetaM Expr)
      withLocalDeclsDND (dataAs.toArray.mapIdx fun i a => (Name.mkSimple s!"hw{i}", mkApp2 invs[i]! a ws[i]!)) fun hws => do
        let wList ← mkListLit (mkConst ``Value) ws.toList
        let envK ← mkAppM ``clauseEnv #[env, nameList, wList]
        let branchT := (mkAppN alts[k]! as).headBeta
        let gb ← mkFreshExprMVar (← mkAppM ``Eval #[envK, bk, mkApp inv branchT])
        let saved := (← get).locals
        for i in [0:dataAs.length] do
          let lv : GLVar := { fvar := dataAs[i]!, cname := names[i]!, value := ws[i]!, rel := hws[i]! }
          modify fun s => { s with locals := s.locals.push lv }
        solve gb.mvarId!
        modify fun s => { s with locals := saved }
        mkLambdaFVars (as ++ #[heq] ++ ws ++ hws) (← instantiateMVars gb)
    lemArgs := lemArgs ++ names.toArray.map (some ∘ mlString) ++ #[some hnd, some bk, some hk]
  assignProof g (← mkAppOptM (d.name ++ `cake_mat) lemArgs)

partial def solveListCases (g : MVarId) (env inv fn : Expr) (args : Array Expr) : GoalM Unit := do
  let ctx ← read
  let α := args[0]!
  let motive := args[1]!
  let major := args[2]!
  let nilAlt := args[3]!
  let consAlt := args[4]!
  let listTy ← mkAppM ``List #[α]
  let dep ← withLocalDeclD `x listTy fun x => do
    return (← instantiateMVars (motive.beta #[x])).headBeta.containsFVar x.fvarId!
  if dep then return ← solveDepCasesNewtype g env inv fn 1 args listTy
  unless major.isFVar do
    let letT := Expr.letE `z listTy major (mkAppN fn #[α, motive, .bvar 0, nilAlt, consAlt]) false
    let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv letT])
    return ← solve g'
  let st ← get
  let some lv := st.locals.find? (·.fvar == major) | throwError "unknown scrutinee {major}"
  let invA ← invOf α
  let invL ← mkAppM ``LIST #[invA]
  let hl ← proveLookupG env lv.cname lv.value ctx.unfoldRec
  let he ← mkAppOptM ``Eval_var #[env, shortIdent lv.cname, lv.value, mkApp invL major, hl, lv.rel]
  let qfun ← withLocalDeclD `x listTy fun x => do
    mkLambdaFVars #[x] (mkApp inv (mkAppN fn #[α, motive, x, nilAlt, consAlt]))
  -- nil branch
  let bn ← mkFreshExprMVar (mkConst ``Exp)
  let emptyN ← mkListLit (mkConst ``VarN) []
  let emptyV ← mkListLit (mkConst ``Value) []
  let hn ← withLocalDeclD `h (← mkEq major (← mkAppOptM ``List.nil #[α])) fun h => do
    let envN ← mkAppM ``clauseEnv #[env, emptyN, emptyV]
    let gb ← mkFreshExprMVar (← mkAppM ``Eval #[envN, bn, mkApp inv nilAlt])
    solve gb.mvarId!
    mkLambdaFVars #[h] (← instantiateMVars gb)
  -- cons branch
  let nx ← freshCName "h"
  let ny ← freshCName "t"
  let hne ← closeWith (mkNot (← mkEq (mlString nx) (mlString ny))) (← `(tactic| decide))
  let bc ← mkFreshExprMVar (mkConst ``Exp)
  let hc ← withLocalDeclD `a α fun a => withLocalDeclD `as listTy fun as => do
    withLocalDeclD `h (← mkEq major (← mkAppM ``List.cons #[a, as])) fun h => do
    withLocalDeclD `w0 (mkConst ``Value) fun w0 => withLocalDeclD `w1 (mkConst ``Value) fun w1 => do
    withLocalDeclD `hw0 (mkApp2 invA a w0) fun hw0 => withLocalDeclD `hw1 (mkApp2 invL as w1) fun hw1 => do
      let envC ← mkAppM ``clauseEnv #[env, ← mkListLit (mkConst ``VarN) [mlString nx, mlString ny],
        ← mkListLit (mkConst ``Value) [w0, w1]]
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[envC, bc, mkApp inv (consAlt.beta #[a, as]).headBeta])
      let saved := (← get).locals
      let la : GLVar := { fvar := a, cname := nx, value := w0, rel := hw0 }
      let las : GLVar := { fvar := as, cname := ny, value := w1, rel := hw1 }
      modify fun s => { s with locals := s.locals.push la |>.push las }
      solve gb.mvarId!
      modify fun s => { s with locals := saved }
      mkLambdaFVars #[a, as, h, w0, w1, hw0, hw1] (← instantiateMVars gb)
  assignProof g (← mkAppOptM ``list_cake_mat #[α, invA, env, ctx.hlist, none, major, he, qfun,
    bn, hn, mlString nx, mlString ny, hne, bc, hc])

/-- Is `e` an application of a `casesOn` the translator handles, with a
non-dependent motive? -/
partial def isSupportedCases (e : Expr) : MetaM Bool := do
  let .const cn _ := e.getAppFn | return false
  if cn == ``Nat.casesOn || cn == ``List.casesOn || cn == ``Bool.casesOn then return true
  let tn := cn.getPrefix
  unless cn == tn ++ `casesOn do return false
  let some (.inductInfo ii) := (← getEnv).find? tn | return false
  let args := e.getAppArgs
  unless args.size == ii.numParams + 1 + 1 + ii.ctors.length do return false
  let major := args[ii.numParams + 1]!
  let τ ← whnfD (← inferType major)
  if (← findDatatype? τ).isSome then return true
  return (← newtypeInfo? τ).isSome

/-- `T.casesOn` for the type of `d`, with a non-dependent motive returning `R`,
whose branches are `branch (C fields)`. -/
partial def mkCasesOn (d R : Expr) (branch : Expr → MetaM Expr) : MetaM Expr := do
  let τ ← whnfD (← inferType d)
  let .const I lvls := τ.getAppFn | throwError "cannot case split on {d} : {τ}"
  let some (.inductInfo ii) := (← getEnv).find? I | throwError "cannot case split on {d} : {τ}"
  let params := τ.getAppArgs
  let uR ← getLevel R
  let motive ← withLocalDeclD `x τ fun x => mkLambdaFVars #[x] R
  let mut alts : Array Expr := #[]
  for c in ii.ctors do
    let cty ← instantiateForall (← instantiateTypeLevelParams (← getConstInfo c).toConstantVal lvls) params
    let alt ← forallTelescope cty fun fs _ => do
      mkLambdaFVars fs (← branch (mkAppN (mkAppN (mkConst c lvls) params) fs))
    alts := alts.push alt
  return mkAppN (mkConst (I ++ `casesOn) (uR :: lvls)) (params ++ #[motive, d] ++ alts)

/-- `f x`: the function part, then the argument, with the function's own
invariant (`Arrow` or `DARROW`). -/
partial def solvePeel (g : MVarId) (env fpart x : Expr) : GoalM Unit := do
  if (← isType x) || (← inferType x).isSort then
    throwError "type argument {x} passed as data in {mkApp fpart x}"
  -- a proof argument: `F h` with `F`'s invariant `PIPROP`, or `F x h` with `DARROWP`
  if ← isProof x then
    -- `F x h` where `F`'s invariant is `DARROWP`
    if fpart.isApp then
      let F := fpart.appFn!
      let xd := fpart.appArg!
      let invF ← invOf (← inferType F)
      if let (``DARROWP, #[_, _, _, invA, _]) := (← whnfR invF).getAppFnArgs then
        let (_, gf) ← newEvalGoal env (mkApp invF F)
        let (_, gx) ← newEvalGoal env (mkApp invA xd)
        solve gf; solve gx
        assignProof g (← mkAppM ``Eval_app_darrowp #[← instantiateMVars (mkMVar gf),
          ← instantiateMVars (mkMVar gx), x])
        return
    -- `F h` where `F`'s invariant is `PIPROP`
    let invF ← invOf (← inferType fpart)
    if let (``PIPROP, _) := (← whnfR invF).getAppFnArgs then
      let (_, gf) ← newEvalGoal env (mkApp invF fpart)
      solve gf
      assignProof g (← mkAppM ``Eval_piprop_elim #[← instantiateMVars (mkMVar gf), x])
      return
    throwError "proof argument {x} to {fpart} (invariant {invF})"
  let invF ← invOf (← inferType fpart)
  let (_, gf) ← newEvalGoal env (mkApp invF fpart)
  solve gf
  match (← whnfR invF).getAppFnArgs with
  | (``Arrow, #[_, _, invA, _]) =>
    let (_, gx) ← newEvalGoal env (mkApp invA x)
    solve gx
    assignProof g (← mkAppM ``Eval_app_arrow #[← instantiateMVars (mkMVar gf), ← instantiateMVars (mkMVar gx)])
  | (``DARROW, #[_, _, invA, _]) =>
    let (_, gx) ← newEvalGoal env (mkApp invA x)
    solve gx
    assignProof g (← mkAppM ``Eval_app_darrow #[← instantiateMVars (mkMVar gf), ← instantiateMVars (mkMVar gx)])
  | _ => throwError "function {fpart} has invariant {invF}"

/-- Case split the goal's term `t` on the local `d`: the term becomes
`T.casesOn d (fun fields => reduce (t[d := C fields]))`, by the equation
proved with `cases d` and `rfl`. -/
partial def splitOn (g : MVarId) (env inv t d : Expr) (reduce : Expr → MetaM Expr) : GoalM Unit := do
  let R ← inferType t
  let q ← mkCasesOn d R fun ctorApp => reduce (t.replaceFVar d ctorApp)
  let eqTy ← mkEq t q
  let mv ← mkFreshExprMVar eqTy
  let subgoals ← mv.mvarId!.cases d.fvarId!
  for sg in subgoals do
    sg.mvarId.refl
  let eqPf ← instantiateMVars mv
  let ce ← evalGoalCe g
  let motive ← withLocalDeclD `t R fun tt => do mkLambdaFVars #[tt] (← mkAppM ``Eval #[env, ce, mkApp inv tt])
  let g' ← g.replaceTargetEq (mkApp motive q).headBeta (← mkCongrArg motive eqPf)
  solve g'

/-- An auxiliary sparse `casesOn` (`…._sparseCasesOn_k`): split on its
scrutinee (its first explicit argument). -/
partial def solveSparseCases (g : MVarId) (env inv t : Expr) : GoalM Unit := do
  let .const cn lvls := t.getAppFn | unreachable!
  let args := t.getAppArgs
  let ci ← getConstInfo cn
  let some idx ← forallTelescope ci.type fun xs _ => do
      for i in [0:xs.size] do
        if (← xs[i]!.fvarId!.getDecl).binderInfo.isExplicit then return some i
      return none
    | throwError "sparse casesOn {cn} without an explicit scrutinee"
  let d := args[idx]!
  let replaceT (t' : Expr) : GoalM MVarId := do
    g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
  unless d.isFVar do
    let letT := Expr.letE `z (← inferType d) d (← discrLetBody t d idx) false
    return ← solve (← replaceT letT)
  splitOn g env inv t d fun t' => do
    let f := t'.getAppFn
    let .const _ lv := f | pure t'
    let _ := lv
    pure (← whnfCore (mkAppN (← instantiateValueLevelParams ci lvls) t'.getAppArgs).headBeta)

/-- A `match`: reduce it if the discriminants decide it; use its compiled
`casesOn` tree when that is supported; otherwise case split on a
discriminant, with the equation `match … = casesOn …` proved by cases. -/
partial def solveMatcher (g : MVarId) (env inv t : Expr) : GoalM Unit := do
  let replaceT (t' : Expr) : GoalM MVarId := do
    g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
  -- reduce only on syntactic constructors/literals: `reduceMatcher?` would put
  -- discriminants in whnf, unfolding definitions into their internals
  let discrsCtor ← do
    let some info ← getMatcherInfo? (t.getAppFn.constName!) | pure false
    let ds := t.getAppArgs[info.numParams + 1 : info.numParams + 1 + info.numDiscrs].toArray
    ds.allM fun d => do
      let d := d.consumeMData
      if d.isLit || d.nat?.isSome || d.rawNatLit?.isSome then return true
      let d ← whnfR d
      -- variables, projections etc. are fine (structure eta); applications of
      -- defined functions are not (whnf would unfold them)
      let .const c _ := d.getAppFn | return true
      return (← getEnv).find? c matches some (.ctorInfo _)
  if discrsCtor then
    if let .reduced t' ← reduceMatcher? t then
      return ← solve (← replaceT t')
  let .const fnName lvls := t.getAppFn | unreachable!
  let args := t.getAppArgs
  -- a `Decidable P` discriminant: split on it
  if let some info ← getMatcherInfo? fnName then
    for i in [0:info.numDiscrs] do
      if ← solveDecSplit g env inv t (info.numParams + 1 + i) then return
  let mci ← getConstInfo fnName
  let unfolded := (mkAppN (← instantiateValueLevelParams mci lvls) args).headBeta
  if ← isSupportedCases unfolded then
    return ← solve (← replaceT unfolded)
  -- a compiled sparse `casesOn` (e.g. literal patterns: cases + decidable tests)
  if let .const un _ := unfolded.getAppFn then
    if let .str _ last := un then
      if last.startsWith "_sparseCasesOn" then
        return ← solve (← replaceT unfolded)
  -- split on a discriminant
  let some info ← getMatcherInfo? fnName | throwError "no matcher info for {fnName}"
  let discrs := args[info.numParams + 1 : info.numParams + 1 + info.numDiscrs].toArray
  let R ← inferType t
  for i in [0:discrs.size] do
    let d := discrs[i]!
    let τ ← whnfD (← inferType d)
    let .const I _ := τ.getAppFn | continue
    let some (.inductInfo _) := (← getEnv).find? I | continue
    -- a constructor application is already split
    if let .const dc _ := d.getAppFn then
      if let some (.ctorInfo _) := (← getEnv).find? dc then continue
    unless d.isFVar do
      -- bind the discriminant: `m … d …` is `let z := d; m … z …`
      let letT := Expr.letE `z (← inferType d) d (← discrLetBody t d (info.numParams + 1 + i)) false
      return ← solve (← replaceT letT)
    return ← splitOn g env inv t d fun t' => do
      match ← reduceMatcher? t' with
      | .reduced r => pure r
      | _ => pure t'
  -- last resort: the matcher's compiled body (e.g. literal patterns: decidable tests)
  if unfolded.getAppFn != t.getAppFn then
    return ← solve (← replaceT unfolded)
  throwError "cannot translate match {t}"

partial def solveApp (g : MVarId) (env inv t : Expr) : GoalM Unit := do
  let ctx ← read
  let fn := t.getAppFn
  let args := t.getAppArgs
  -- `casesOn` of a constructor application (after reducible unfolding): iota-reduce
  if let .const cn _ := fn then
    let tn := cn.getPrefix
    if cn == tn ++ `casesOn then
      if let some (.inductInfo ii) := (← getEnv).find? tn then
        if args.size > ii.numParams + 1 + ii.numIndices then
          let major ← whnfR args[ii.numParams + 1 + ii.numIndices]!
          if let .const mc _ := major.getAppFn then
            if (← getEnv).find? mc matches some (.ctorInfo _) then
              let t' ← whnfR t
              if t' != t then
                return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t']))
  -- under-applied `casesOn` (as a function value): eta-expand to its full arity
  if let .const cn _ := fn then
    if isAuxRecursor (← getEnv) cn then
      let arity ← forallTelescope (← inferType fn) fun xs _ => pure xs.size
      if args.size < arity then
        let t' ← forallTelescope (← inferType t) fun xs _ => do
          let xs := xs[:arity - args.size].toArray
          mkLambdaFVars xs (mkAppN t xs)
        return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t']))
  -- under-applied constructors (constructors as function values): eta-expand
  if let .const cn _ := fn then
    if let some (.ctorInfo ci) := (← getEnv).find? cn then
      if args.size ≥ ci.numParams && args.size < ci.numParams + ci.numFields then
        let t' ← forallTelescope (← inferType t) fun xs _ => do
          let xs := xs[:ci.numParams + ci.numFields - args.size].toArray
          mkLambdaFVars xs (mkAppN t xs)
        return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t']))
  -- replacements under runtime assumptions (hypotheses `∀ xs, K xs = K' xs`)
  if let .const c _ := fn then
    if let some (_, rc, hyp) := ctx.assumed.find? (·.1 == c) then
      let n ← forallTelescope (← inferType hyp) fun xs _ => pure xs.size
      if args.size == n then
        let heq := mkAppN hyp args
        let t' := mkAppN (mkConst rc) args
        let ce ← evalGoalCe g
        let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv t'])
        solve gb.mvarId!
        let motive ← withLocalDeclD `x (← inferType t) fun x => do
          mkLambdaFVars #[x] (← mkAppM ``Eval #[env, ce, mkApp inv x])
        g.assign (← mkEqMP (← mkCongrArg motive (← mkEqSymm heq)) (← instantiateMVars gb))
        return
  -- quotients: `Quot.mk r a` is `a`'s value; `Quot.lift f h q` applies `f` to `q`
  if fn.isConstOf ``Quot.mk && args.size == 3 then
    let (``QUOT, #[_, _, invA]) := (← whnfR inv).getAppFnArgs | throwError "quotient without QUOT invariant: {inv}"
    let (_, ga) ← newEvalGoal env (mkApp invA args[2]!)
    solve ga
    assignProof g (← mkAppOptM ``Eval_quot_mk #[none, args[1]!, invA, env, none, none, ← instantiateMVars (mkMVar ga)])
    return
  if fn.isConstOf ``Quot.lift && args.size ≥ 6 then
    if args.size > 6 then return ← solvePeel g env (mkAppN fn args.pop) args.back!
    let q := args[5]!
    let invQ ← invOf (← inferType q)
    let (``QUOT, #[_, _, invA]) := invQ.getAppFnArgs | throwError "quotient without QUOT invariant"
    let f := args[3]!
    let (_, gf) ← newEvalGoal env (mkApp (← mkAppM ``Arrow #[invA, inv]) f)
    solve gf
    let (_, gq) ← newEvalGoal env (mkApp invQ q)
    solve gq
    assignProof g (← mkAppOptM ``Eval_quot_lift #[none, none, none, invA, inv, env, none, none, f, args[4]!, q,
      ← instantiateMVars (mkMVar gf), ← instantiateMVars (mkMVar gq)])
    return
  -- rewrite rules `lhs = rhs` whose `lhs` matches
  if let .const c _ := fn then
    if let some thms := (rewriteExt.getState (← getEnv)).find? c then
      for thm in thms do
        let ci ← getConstInfo thm
        let thmE ← mkConstWithFreshMVarLevels thm
        let (xs, _, ty) ← forallMetaTelescope (← inferType thmE)
        let _ := ci
        let some (_, lhs, rhs) := ty.eq? | continue
        let saved : Meta.SavedState ← (Meta.saveState : MetaM _)
        if (← isDefEq lhs t) then
          let heq ← instantiateMVars (mkAppN thmE xs)
          if heq.hasExprMVar then (saved.restore : MetaM Unit); continue
          let t' ← instantiateMVars rhs
          let ce ← evalGoalCe g
          let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv t'])
          solve gb.mvarId!
          let motive ← withLocalDeclD `x (← inferType t) fun x => do
            mkLambdaFVars #[x] (← mkAppM ``Eval #[env, ce, mkApp inv x])
          g.assign (← mkEqMP (← mkCongrArg motive (← mkEqSymm heq)) (← instantiateMVars gb))
          return
        (saved.restore : MetaM Unit)
  -- registered replacements `K xs = K' xs`
  if let .const c us := fn then
    if let some (rc, thm) := (replaceExt.getState (← getEnv)).find? c then
      let n ← forallTelescope (← inferType (mkConst thm us)) fun xs _ => pure xs.size
      if args.size == n then
        let heq := mkAppN (mkConst thm us) args
        let t' := mkAppN (mkConst rc us) args
        let ce ← evalGoalCe g
        let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv t'])
        solve gb.mvarId!
        let motive ← withLocalDeclD `x (← inferType t) fun x => do
          mkLambdaFVars #[x] (← mkAppM ``Eval #[env, ce, mkApp inv x])
        g.assign (← mkEqMP (← mkCongrArg motive (← mkEqSymm heq)) (← instantiateMVars gb))
        return
  -- matchers and sparse casesOn auxiliaries
  if let .const fnName _ := fn then
    if (← Meta.isMatcher fnName) then
      return ← solveMatcher g env inv t
    if let .str _ last := fnName then
      if last.startsWith "_sparseCasesOn" then
        return ← solveSparseCases g env inv t
  -- Nat.add / Nat.mul as primitives (also reached after unfolding `+`, `*`)
  if (fn.isConstOf ``Nat.add || fn.isConstOf ``Nat.mul) && args.size == 2 then
    let lem := if fn.isConstOf ``Nat.add then ``Eval_nat_add else ``Eval_nat_mul
    let (_, ga) ← newEvalGoal env (mkApp (mkConst ``NAT) args[0]!)
    let (_, gb) ← newEvalGoal env (mkApp (mkConst ``NAT) args[1]!)
    solve ga; solve gb
    assignProof g (← mkAppM lem #[← instantiateMVars (mkMVar ga), ← instantiateMVars (mkMVar gb)])
    return
  -- class methods applied to instances: unfold to the instance's implementation
  if let some t' ← Meta.unfoldProjInst? t then
    let t' := t'.headBeta
    if t' != t then
      let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
      return ← solve g'
  -- conditions as Bool: known comparisons, else the instance (a newtype)
  if fn.isConstOf ``Decidable.decide && args.size == 2 then
    let saved : Meta.SavedState ← (Meta.saveState : MetaM _)
    let st₀ ← get
    try return ← solveDecide g env args[0]!
    catch _ =>
      (saved.restore : MetaM Unit)
      set st₀
    let t' := Expr.proj ``Decidable 0 args[1]!
    let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
    return ← solve g'
  -- casts: unfold to `Eq.rec`, which is the identity on values
  if let .const cn lvls := fn then
    if [``Eq.ndrec, ``Eq.mpr, ``Eq.mp, ``cast, ``Eq.ndrec_symm, ``Eq.recOn, ``Eq.casesOn].contains cn then
      let ci ← getConstInfo cn
      if ci.hasValue then
        let t' := (mkAppN (← instantiateValueLevelParams ci lvls) args).headBeta
        let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
        return ← solve g'
  if fn.isConstOf ``Eq.rec && args.size ≥ 6 then
    let α := args[0]!
    let a := args[1]!
    let motive := args[2]!
    let m := args[3]!
    let b := args[4]!
    let h := args[5]!
    if args.size > 6 then throwError "over-applied cast {t}"
    let I ← withLocalDeclD `b α fun bv => do
      withLocalDeclD `h (← mkEq a bv) fun hv => do
        mkLambdaFVars #[bv, hv] (← invOf (mkApp2 motive bv hv))
    let (_, gm) ← newEvalGoal env (mkApp (I.beta #[a, ← mkEqRefl a]) m)
    solve gm
    assignProof g (← mkAppOptM ``Eval_eqrec #[α, a, motive, I, env, none, m, b, h,
      ← instantiateMVars (mkMVar gm)])
    return
  -- `Bool.rec (motive := fun x => x.Reflects P → R) F T b r …`: a decision taken apart, i.e. `dite`
  if (fn.isConstOf ``Bool.rec || fn.isConstOf ``Bool.casesOn) && args.size ≥ 5 then
    let motive := args[0]!
    let isRefl ← withLocalDeclD `x (mkConst ``Bool) fun x => do
      let m ← whnfR (motive.beta #[x]).headBeta
      if let .forallE _ dom body _ := m then
        if let (``Bool.Reflects, #[xb, P]) := dom.getAppFnArgs then
          if xb == x && !body.hasLooseBVars && !body.containsFVar x.fvarId! && !P.containsFVar x.fvarId! then
            return some (P, body)
      return none
    if let some (P, R) := isRefl then
      let (F, T, b, r) := if fn.isConstOf ``Bool.rec then (args[1]!, args[2]!, args[3]!, args[4]!)
        else (args[2]!, args[3]!, args[1]!, args[4]!)
      let heq ← if fn.isConstOf ``Bool.rec then mkAppOptM ``bool_rec_reflects_eq_dite #[P, R, F, T, b, r]
        else mkAppOptM ``bool_casesOn_reflects_eq_dite #[P, R, F, T, b, r]
      let rest := args[5:].toArray
      let t5 := mkAppN fn args[:5].toArray
      let d5 := (← inferType heq).appArg!
      let t' := mkAppN d5 rest
      let ce ← evalGoalCe g
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv t'])
      solve gb.mvarId!
      let motiveE ← withLocalDeclD `w R fun w => do mkLambdaFVars #[w] (← mkAppM ``Eval #[env, ce, mkApp inv (mkAppN w rest)])
      let _ := t5
      g.assign (← mkEqMP (← mkCongrArg motiveE (← mkEqSymm heq)) (← instantiateMVars gb))
      return
  -- Bool.rec / Bool.casesOn / cond with a non-dependent motive: `if b then t else f`
  if (fn.isConstOf ``Bool.rec && args.size == 4) || (fn.isConstOf ``Bool.casesOn && args.size == 4) ||
      (fn.isConstOf ``cond && args.size == 4) then
    let (b, f, tt) := if fn.isConstOf ``Bool.rec then (args[3]!, args[1]!, args[2]!)
      else if fn.isConstOf ``Bool.casesOn then (args[1]!, args[2]!, args[3]!)
      else (args[1]!, args[3]!, args[2]!)
    let t' ← mkAppOptM ``Bool.rec #[← withLocalDeclD `x (mkConst ``Bool) fun x => do
      mkLambdaFVars #[x] (← inferType f), f, tt, b]
    let (_, gb) ← newEvalGoal env (mkApp (mkConst ``BOOL) b)
    solve gb
    let ceT ← mkFreshExprMVar (mkConst ``Exp)
    let ceF ← mkFreshExprMVar (mkConst ``Exp)
    let hf ← withLocalDeclD `h (← mkEq b (mkConst ``Bool.false)) fun h => do
      let g' ← mkFreshExprMVar (← mkAppM ``Eval #[env, ceF, mkApp inv f])
      solve g'.mvarId!
      mkLambdaFVars #[h] (← instantiateMVars g')
    let ht ← withLocalDeclD `h (← mkEq b (mkConst ``Bool.true)) fun h => do
      let g' ← mkFreshExprMVar (← mkAppM ``Eval #[env, ceT, mkApp inv tt])
      solve g'.mvarId!
      mkLambdaFVars #[h] (← instantiateMVars g')
    let pf ← mkAppOptM ``Eval_bool_rec #[none, inv, env, none, ceT, ceF, b, f, tt,
      ← instantiateMVars (mkMVar gb), hf, ht]
    let g ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
    assignProof g pf
    return
  -- dependent if-then-else: the branches see the condition (or its negation)
  if fn.isConstOf ``dite && args.size == 5 then
    let (_, gc) ← newEvalGoal env (mkApp (mkConst ``BOOL) (← mkAppOptM ``decide #[args[1]!, args[2]!]))
    solve gc
    let ce₁ ← mkFreshExprMVar (mkConst ``Exp)
    let ce₂ ← mkFreshExprMVar (mkConst ``Exp)
    let h₁ ← withLocalDeclD `h args[1]! fun h => do
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce₁, mkApp inv (args[3]!.beta #[h])])
      solve gb.mvarId!
      mkLambdaFVars #[h] (← instantiateMVars gb)
    let h₂ ← withLocalDeclD `h (mkNot args[1]!) fun h => do
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce₂, mkApp inv (args[4]!.beta #[h])])
      solve gb.mvarId!
      mkLambdaFVars #[h] (← instantiateMVars gb)
    assignProof g (← mkAppOptM ``Eval_dite #[args[0]!, inv, env, args[1]!, args[2]!, none, ce₁, ce₂,
      args[3]!, args[4]!, ← instantiateMVars (mkMVar gc), h₁, h₂])
    return
  -- if-then-else
  if fn.isConstOf ``ite && args.size == 5 then
    let (_, gc) ← newEvalGoal env (mkApp (mkConst ``BOOL) (← mkAppOptM ``decide #[args[1]!, args[2]!]))
    solve gc
    let ce₁ ← mkFreshExprMVar (mkConst ``Exp)
    let ce₂ ← mkFreshExprMVar (mkConst ``Exp)
    let h₁ ← withLocalDeclD `h args[1]! fun h => do
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce₁, mkApp inv args[3]!])
      solve gb.mvarId!
      mkLambdaFVars #[h] (← instantiateMVars gb)
    let h₂ ← withLocalDeclD `h (mkNot args[1]!) fun h => do
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce₂, mkApp inv args[4]!])
      solve gb.mvarId!
      mkLambdaFVars #[h] (← instantiateMVars gb)
    assignProof g (← mkAppOptM ``Eval_ite #[args[0]!, inv, env, args[1]!, args[2]!, none, ce₁, ce₂,
      args[3]!, args[4]!, ← instantiateMVars (mkMVar gc), h₁, h₂])
    return
  -- newtypes: constructor, projection functions, casesOn
  if let .const cn _ := fn then
    if let some (.ctorInfo ci) := (← getEnv).find? cn then
      if let some (I, j, _) ← newtypeInfo? (← inferType t) then
        if I == ci.induct && args.size == ci.numParams + ci.numFields then
          let field := args[ci.numParams + j]!
          let invF ← invOf (← inferType field)
          let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp invF field])
          return ← solve g'
    if let some info ← getProjectionFnInfo? cn then
      if args.size == info.numParams + 1 then
        let some (.ctorInfo ci) := (← getEnv).find? info.ctorName | throwError "bad projection {cn}"
        let t' := mkAppN (.proj ci.induct info.i args[info.numParams]!) args[info.numParams + 1:].toArray
        let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
        return ← solve g'
    let tn := cn.getPrefix
    if cn == tn ++ `casesOn then
      if let some (.inductInfo ii) := (← getEnv).find? tn then
        -- `Decidable.casesOn d …`: split on `d` (its fields are a Boolean and a proof about it)
        if tn == ``Decidable && args.size ≥ ii.numParams + 3 then
          if ← solveDecSplit g env inv t (ii.numParams + 1) then return
        -- structure eta: `S.casesOn s f = f s.1 … s.n` for any non-recursive structure
        if ii.ctors.length == 1 && ii.numIndices == 0 && !ii.isRec && args.size ≥ ii.numParams + 3 then
          let major := args[ii.numParams + 1]!
          let mty ← whnfD (← inferType major)
          -- registered datatypes have their own `casesOn` (and projections become `casesOn`)
          if !(← isProp (← inferType major)) && (mty.hasFVar || (← findDatatype? mty).isNone) then
            let some (.ctorInfo ci) := (← getEnv).find? ii.ctors.head! | unreachable!
            let projs := (List.range ci.numFields).map fun i => Expr.proj tn i major
            let t' := (mkAppN (mkAppN args[ii.numParams + 2]! projs.toArray)
              args[ii.numParams + 3:].toArray).headBeta
            let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
            return ← solve g'
  -- lists
  if fn.isConstOf ``List.nil && args.size == 1 then
    let (``LIST, #[_, invA]) := (← whnfR inv).getAppFnArgs | throwError "list without LIST invariant"
    assignProof g (← mkAppOptM ``Eval_nil #[args[0]!, invA, env, ctx.hlist])
    return
  if fn.isConstOf ``List.cons && args.size == 3 then
    let (``LIST, #[_, invA]) := (← whnfR inv).getAppFnArgs | throwError "list without LIST invariant"
    -- the whole cons chain, solved element by element (no nesting: long literals)
    let mut elems : Array Expr := #[]
    let mut tl := t
    while tl.isAppOfArity ``List.cons 3 do
      elems := elems.push tl.appFn!.appArg!
      tl := tl.appArg!
    let mut pfs : Array Expr := #[]
    for e in elems do
      let (_, ge) ← newEvalGoal env (mkApp invA e)
      solve ge
      pfs := pfs.push (← instantiateMVars (mkMVar ge))
    let (_, gt) ← newEvalGoal env (mkApp inv tl)
    solve gt
    let mut acc ← instantiateMVars (mkMVar gt)
    let mut rest := tl
    for i in (List.range elems.size).reverse do
      acc ← mkAppOptM ``Eval_cons #[args[0]!, invA, env, ctx.hlist, none, none, elems[i]!, rest, pfs[i]!, acc]
      rest ← mkAppOptM ``List.cons #[args[0]!, elems[i]!, rest]
    assignProof g acc
    return
  if fn.isConstOf ``List.casesOn && args.size == 5 then
    return ← solveListCases g env inv fn args
  -- constructors of datatypes
  if let .const cn _ := fn then
    if let some (.ctorInfo ci) := (← getEnv).find? cn then
      let τ ← whnfR (← inferType t)
      if !τ.hasFVar then
        if let some d ← findDatatype? τ then
          let some k := d.ctors.findIdx? (·.1 == cn) | throwError "constructor {cn} not in {τ}"
          let (_, _, dataFlags) := d.ctors[k]!
          let some hc := ctx.hasCons.find? d.name | throwError "no constructor environment for {τ}"
          let fields := args[ci.numParams:].toArray
          let mut pfs : Array Expr := #[]
          for j in [0:fields.size] do
            if dataFlags[j]! then
              let fty ← inferType fields[j]!
              let fi := if fty == τ then mkConst (d.name ++ `cakeInv)
                else mkConst (d.name ++ Name.mkSimple s!"f{k}_{j}")
              let (_, gj) ← newEvalGoal env (mkApp fi fields[j]!)
              solve gj
              pfs := pfs.push (← instantiateMVars (mkMVar gj))
          let nd := pfs.size
          let lemArgs : Array (Option Expr) := #[some env, some hc] ++ Array.replicate nd none ++
            fields.map some ++ pfs.map some
          assignProof g (← mkAppOptM (d.name ++ Name.mkSimple s!"con{k}") lemArgs)
          return
  -- casesOn of datatypes, with a non-dependent motive
  if let .const cn _ := fn then
    let tn := cn.getPrefix
    if cn == tn ++ `casesOn then
      if let some (.inductInfo ii) := (← getEnv).find? tn then
        if args.size > ii.numParams + 1 then
          -- `whnfD`: the major's type may be behind a definition (e.g. `Id (ForInStep β)`)
          let τ ← whnfD (← inferType args[ii.numParams + 1]!)
          if let some d ← findDatatype? τ then
            return ← solveCases g env inv d fn ii.numParams args
          -- not registered yet: request it (closed types, non-dependent motive), rather than fall through
          let motive := args[ii.numParams]!
          let depMotive ← withLocalDeclD `x τ fun x => do
            return (← instantiateMVars (motive.beta #[x])).headBeta.containsFVar x.fvarId!
          if !depMotive && !τ.hasFVar && !(← isProp τ) && (← newtypeInfo? τ).isNone then
            let _ ← invOf τ
  -- `Nat.rec` whose step ignores the induction hypothesis is `Nat.casesOn`
  if fn.isConstOf ``Nat.rec && args.size == 4 then
    if let .lam n nty (.lam _ _ body _) bi := args[2]! then
      if !body.hasLooseBVar 0 then
        let step := Expr.lam n nty (body.lowerLooseBVars 1 1) bi
        let .const _ lvls := fn | unreachable!
        let t' := mkAppN (mkConst ``Nat.casesOn lvls) #[args[0]!, args[3]!, args[1]!, step]
        let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
        return ← solve g'
  -- Nat.casesOn with a non-dependent motive
  if fn.isConstOf ``Nat.casesOn && args.size == 4 then
    let n := args[1]!
    let mn ← freshCName
    let (_, gn) ← newEvalGoal env (mkApp (mkConst ``NAT) n)
    solve gn
    let cez ← mkFreshExprMVar (mkConst ``Exp)
    let ces ← mkFreshExprMVar (mkConst ``Exp)
    let hz ← withLocalDeclD `h (← mkEq n (mkNatLit 0)) fun h => do
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, cez, mkApp inv args[2]!])
      solve gb.mvarId!
      mkLambdaFVars #[h] (← instantiateMVars gb)
    let hs ← withLocalDeclD `m (mkConst ``Nat) fun m => do
      withLocalDeclD `h (← mkEq n (← mkAppM ``HAdd.hAdd #[m, mkNatLit 1])) fun h => do
      withLocalDeclD `mv (mkConst ``Value) fun mv => do
      withLocalDeclD `hm (mkApp2 (mkConst ``NAT) m mv) fun hm => do
        let env' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsBind #[mlString mn, mv, ← mkAppM ``SemEnv.v #[env]],
          ← mkAppM ``SemEnv.c #[env]]
        let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env', ces, mkApp inv (args[3]!.beta #[m])])
        modify fun s => { s with locals := s.locals.push { fvar := m, cname := mn, value := mv, rel := hm } }
        solve gb.mvarId!
        modify fun s => { s with locals := s.locals.pop }
        mkLambdaFVars #[m, h, mv, hm] (← instantiateMVars gb)
    assignProof g (← mkAppOptM ``Eval_nat_casesOn #[none, inv, env, none, cez, ces, mlString mn, n,
      args[2]!, args[3]!, ← instantiateMVars (mkMVar gn), hz, hs])
    return
  -- pairs
  if fn.isConstOf ``Prod.mk && args.size == 4 then
    let (``PAIR, #[_, _, invA, invB]) := (← whnfR inv).getAppFnArgs
      | throwError "pair without a PAIR invariant: {inv}"
    let (_, ga) ← newEvalGoal env (mkApp invA args[2]!)
    let (_, gb) ← newEvalGoal env (mkApp invB args[3]!)
    solve ga; solve gb
    assignProof g (← mkAppM ``Eval_pair #[← instantiateMVars (mkMVar ga), ← instantiateMVars (mkMVar gb)])
    return
  -- Nat arithmetic
  match t.getAppFnArgs with
  | (``HAdd.hAdd, #[ty, _, _, _, a, b]) | (``HMul.hMul, #[ty, _, _, _, a, b]) =>
    if (← whnfR ty).isConstOf ``Nat then
      let lem := if t.isAppOf ``HAdd.hAdd then ``Eval_nat_add else ``Eval_nat_mul
      let (_, ga) ← newEvalGoal env (mkApp (mkConst ``NAT) a)
      let (_, gb) ← newEvalGoal env (mkApp (mkConst ``NAT) b)
      solve ga; solve gb
      assignProof g (← mkAppM lem #[← instantiateMVars (mkMVar ga), ← instantiateMVars (mkMVar gb)])
      return
  | _ => pure ()
  -- a recursive call in a well-founded functional: the call, with Lean's decreasing proof
  if let some r := ctx.rec? then
    if fn.isConstOf ``recCall && args.size == 6 then
      let _ := r
      let t' ← Meta.transform (args[3]!.beta #[args[4]!]).headBeta (post := fun x => do
        if let .proj _ i sv := x then
          if let some v ← Meta.projectCore? sv.consumeMData i then return .done v
        return .continue)
      decHintRef.set (some args[5]!)
      return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t']))
  -- calls to members of the mutual block: the joint induction hypothesis at `inj_j y`
  if let some mr := ctx.mrec? then
    if let .const cn _ := fn then
      if let some m := mr.members.find? (·.head == cn) then
        if args.size == m.arity then
          let y ← if m.arity == 1 then pure args[0]! else
            args.pop.foldrM (fun a acc => mkAppM ``Prod.mk #[a, acc]) args.back!
          let q := (m.inj.beta #[y]).headBeta
          let relTy := mkApp2 mr.r q mr.s
          let hdec ← try closeWith relTy (← `(tactic| (subst_vars; (try simp only [WellFoundedRelation.rel, measure, InvImage, invImage, Nat.lt_wfRel] at *); (try dsimp only at *); first | omega | decreasing_tactic | (simp_wf; omega))))
            catch _ => throwError "cannot prove the mutual call decreases: {← whnfR relTy}"
          let ihq := mkApp2 mr.ih q hdec
          let (_, gx) ← newEvalGoal env (mkApp m.invT y)
          solve gx
          let hl ← proveLookupG env m.cname m.cl ctx.unfoldRec
          let clEq ← withLocalDeclD `w (mkConst ``Value) fun w => do mkLambdaFVars #[w] (← mkEq w m.cl)
          let hf ← mkAppOptM ``Eval_var #[env, shortIdent m.cname, m.cl, clEq, hl, ← mkEqRefl m.cl]
          assignProof g (← mkAppOptM ``Eval_app_ih #[none, none, m.invT, m.invB, env, none, none, m.cl, m.ft, y,
            hf, ← instantiateMVars (mkMVar gx), ihq])
          return
  -- recursive calls
  if let some r := ctx.rec? then
    if fn.isConstOf r.head && args.size == r.static.size + r.arity &&
        (args[:r.static.size].toArray == r.static) then
      let ys := args[r.static.size:].toArray
      let y ← if r.arity == 1 then pure ys[0]! else
        ys.pop.foldrM (fun a acc => mkAppM ``Prod.mk #[a, acc]) ys.back!
      -- the IH at y: ∀ yv, A y yv → AppReturns cl yv (B (f y))
      let ihTy ← whnfR (← inferType r.ih)
      let .forallE _ _ body _ := ihTy | throwError "bad IH"
      let .forallE _ relTy _ _ := body.instantiate1 y | throwError "bad IH"
      let hint ← decHintRef.get
      decHintRef.set none
      let hinted ← match hint with
        | none => pure none
        | some h => do
          let hty ← inferType h
          if ← isDefEq hty relTy then pure (some h) else
          try
            let imp ← closeWith (← mkArrow hty relTy) (← `(tactic| (intro hh; subst_vars; exact hh)))
            pure (some (mkApp imp h))
          catch _ => pure none
      let hdec ← if let some h := hinted then pure h else
        try closeWith relTy (← `(tactic| first
          | decreasing_tactic
          | (simp_wf; omega)
          | (simp only [InvImage, Nat.lt_eq] at *; omega)
          | (subst_vars; simp_wf; omega)
          | (subst_vars; simp only [WellFoundedRelation.rel, measure, InvImage, invImage, Nat.lt_wfRel] at *; omega)
          | (subst_vars; simp_wf; decreasing_tactic)))
        catch _ =>
          let hyps ← (← getLCtx).foldlM (init := m!"") fun acc d => do
            if d.isImplementationDetail then return acc
            if ← isProp d.type then return acc ++ m!"\n  {d.userName} : {d.type}" else return acc
          throwError "cannot prove the recursive call decreases: {← whnfR relTy}\nhypotheses:{hyps}"
      let ihy := mkApp2 r.ih y hdec
      let ihyTy ← whnfR (← inferType ihy)
      let .forallE _ _ ihB _ := ihyTy | throwError "bad IH at y"
      let .forallE _ invAy _ _ := ihB | throwError "bad IH at y"
      let invA := invAy.appFn!.appFn!
      let (_, gx) ← newEvalGoal env (mkApp invA y)
      solve gx
      let hl ← proveLookupG env r.cname r.cl ctx.unfoldRec
      let clEq ← withLocalDeclD `w (mkConst ``Value) fun w => do mkLambdaFVars #[w] (← mkEq w r.cl)
      let hf ← mkAppOptM ``Eval_var #[env, shortIdent r.cname, r.cl, clEq, hl, ← mkEqRefl r.cl]
      if let some (invBf, ft) := r.dep? then
        assignProof g (← mkAppOptM ``Eval_app_ihd #[none, none, invA, invBf, env, none, none, r.cl, ft, y,
          hf, ← instantiateMVars (mkMVar gx), ihy])
        return
      assignProof g (← mkAppOptM ``Eval_app_ih #[none, none, invA, inv, env, none, none, r.cl, none, y,
        hf, ← instantiateMVars (mkMVar gx), ihy])
      return
  -- applications of locals and globals: peel the last argument
  -- Nat constructors
  if t.isConstOf ``Nat.zero then
    assignProof g (← mkAppM ``Eval_nat_lit #[env, toExpr (0 : Nat)])
    return
  if fn.isConstOf ``Nat.succ && args.size == 1 then
    let t' ← mkAppM ``HAdd.hAdd #[args[0]!, mkNatLit 1]
    let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
    return ← solve g'
  -- unit value
  if t.isConstOf ``Unit.unit || t.isConstOf ``PUnit.unit then
    assignProof g (← mkAppM ``Eval_unit #[env])
    return
  -- non-recursive definitions with an open (local-dependent) implicit or type argument
  -- (e.g. `@Decidable.isTrue (a = b) h`): no closed unit key, so unfold in place
  if let .const cn lvls := fn then
    if let some (.defnInfo di) := (← getEnv).find? cn then
      let lenv ← getEnv
      let isRec := (Lean.Elab.Structural.eqnInfoExt.find? lenv cn).isSome || (Lean.Elab.WF.eqnInfoExt.find? lenv cn).isSome
      if !isRec && !(← Meta.isMatcher cn) && !(replaceExt.getState lenv).contains cn &&
          !(isAuxRecursor lenv cn) && !(isNoConfusion lenv cn) then
        let openStatic ← forallBoundedTelescope di.type args.size fun xs _ => do
          let mut r := false
          for i in [0:xs.size] do
            let d ← xs[i]!.fvarId!.getDecl
            let ty ← whnfD d.type
            if (d.binderInfo.isImplicit || d.binderInfo.isInstImplicit || d.binderInfo.isStrictImplicit ||
                ty.isSort) && args[i]!.hasFVar then r := true
          return r
        if openStatic || cn == ``Decidable.isTrue || cn == ``Decidable.isFalse then
          let t' := (mkAppN (← instantiateValueLevelParams (.defnInfo di) lvls) args).headBeta
          return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t']))
  -- constants translated as thunks: `c ()`
  if fn.isConst then
    if let some (key, dargs) ← splitKey t then
      if dargs.isEmpty then
        if let some u := getUnit? (← getEnv) key then
          if let .thunk _ _ := u.kind then
            let some gv := ctx.globals.get? key | throwNeedUnit key
            let hl ← proveLookupG env gv.cname gv.value ctx.unfoldRec
            let tgt ← withLocalDeclD `u (mkConst ``Unit) fun x => mkLambdaFVars #[x] key
            let hf ← mkAppOptM ``Eval_var #[env, shortIdent gv.cname, gv.value, mkApp gv.inv tgt, hl, gv.cert]
            let hx ← mkAppM ``Eval_unit #[env]
            assignProof g (← mkAppM ``Eval_app_arrow #[hf, hx])
            return
  -- under-applied tupled global units (as function values): eta-expand
  if fn.isConst then
    if let some (key, dargs) ← splitKey t then
      if let some u := getUnit? (← getEnv) key then
        if let .function _ _ true := u.kind then
          let arity ← forallTelescope (← inferType key) fun xs _ => pure xs.size
          if dargs.size < arity then
            let t' ← forallTelescope (← inferType t) fun xs _ => do
              let xs := xs[:arity - dargs.size].toArray
              mkLambdaFVars xs (mkAppN t xs)
            return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t']))
  -- fully applied tupled global units: call the tupled closure with a tuple
  if fn.isConst then
    if let some (key, dargs) ← splitKey t then
      if let some u := getUnit? (← getEnv) key then
        if let .function _ _ true := u.kind then
          let tupFn := mkConst (u.name ++ `tupled)
          let arity ← forallTelescope (← inferType key) fun xs _ => pure xs.size
          if dargs.size == arity then
            let tup ← dargs.pop.foldrM (fun a acc => mkAppM ``Prod.mk #[a, acc]) dargs.back!
            let some gv := ctx.globals.get? key | throwNeedUnit key
            let hl ← proveLookupG env gv.cname gv.value ctx.unfoldRec
            let hf ← mkAppOptM ``Eval_var #[env, shortIdent gv.cname, gv.value, mkApp gv.inv tupFn, hl, gv.cert]
            if let (``DARROW, #[_, _, invT, _]) := gv.inv.getAppFnArgs then
              let (_, gt) ← newEvalGoal env (mkApp invT tup)
              solve gt
              assignProof g (← mkAppM ``Eval_app_darrow #[hf, ← instantiateMVars (mkMVar gt)])
              return
            let (``Arrow, #[_, _, invT, _]) := gv.inv.getAppFnArgs | throwError "tupled unit invariant"
            let (_, gt) ← newEvalGoal env (mkApp invT tup)
            solve gt
            assignProof g (← mkAppM ``Eval_app_arrow #[hf, ← instantiateMVars (mkMVar gt)])
            return
  -- applications of global units: the key, then the data arguments
  if fn.isConst then
    if let some (key, dargs) ← splitKey t then
      if dargs.isEmpty then
        let some gv := ctx.globals.get? key | throwNeedUnit key
        let hl ← proveLookupG env gv.cname gv.value ctx.unfoldRec
        assignProof g (← mkAppOptM ``Eval_var #[env, shortIdent gv.cname, gv.value, mkApp gv.inv key, hl, gv.cert])
        return
      return ← solvePeel g env (mkAppN key dargs.pop) dargs.back!
  -- applications of local functions
  if fn.isFVar && args.size > 0 then
    return ← solvePeel g env (mkAppN fn args.pop) args.back!
  throwError "cannot translate {t}"

end

end ConPastel.Translator.Meta
