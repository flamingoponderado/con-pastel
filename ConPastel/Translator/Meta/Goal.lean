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
  /-- A lazy field (`cake_lazy`): `rel` is `LAZY A x value`, and reading the
  variable applies it to `()`. -/
  lazy : Bool := false

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
  /-- A parallel round of member solves: a missing global unit is recorded (in
  `needUnitsAllRef`) and its goal closed by `sorry` instead of aborting, so that
  one round finds all of them. Such a round's result is always discarded. -/
  collectNeeds : Bool := false

structure GSt where
  locals : Array GLVar := #[]
  fresh : Nat := 0
  /-- Lean's own decreasing proof for the recursive call being translated
  (per solve, so that member solves can run in parallel threads). -/
  decHint : Option Expr := none
  /-- The next monadic goal is solved as a plain value (the inside of a
  pushed application, `solveMonadic`). -/
  skipMonadic : Bool := false
  /-- Inside a constructor branch of a match on the local `major`: the
  constructor applied to the branch's fields, the local, and `major = C fields`.
  Lean writes a wildcard arm `| e => … e …` as `C fields` in each constructor's
  branch; that term is translated as `major`'s value, not rebuilt (a rebuilt
  node recomputes its cached fields and gets a fresh identity token). -/
  aliases : Array (Expr × GLVar × Expr) := #[]

abbrev GoalM := StateRefT GSt (ReaderT GCtx MetaM)

/-- The translation needs the unit for `key` first. -/
def needUnitTag : String := "cake: need unit "

initialize needUnitRef : IO.Ref (Option Expr) ← IO.mkRef none


/-- The `n` components of a packed (`PSigma`) argument tuple. -/
partial def psigmaComps (e : Expr) (n : Nat) : Array Expr :=
  if n ≤ 1 then #[e] else
  match e.consumeMData.getAppFnArgs with
  | (``PSigma.mk, #[_, _, a, b]) => #[a] ++ psigmaComps b (n - 1)
  | _ => #[Expr.proj ``PSigma 0 e] ++ psigmaComps (Expr.proj ``PSigma 1 e) (n - 1)

/-- A missing global unit in a collecting round: record it, close `g` by `sorry`. -/
def recordNeedUnit (g : MVarId) (key : Expr) (t : Expr) : MetaM Unit := do
  needUnitsAllRef.modify (·.push key)
  cakeLog s!"[need-unit] {((← ppExpr key).pretty.replace "\n" " ").take 200} for term {((← ppExpr t).pretty.replace "\n" " ").take 200} (collected)"
  -- the goal's CakeML expression gets a placeholder too, so later steps see a term
  let ty := (← instantiateMVars (← g.getType)).headBeta
  if let (``Eval, #[_, Expr.mvar m, _]) := ty.getAppFnArgs then
    unless ← m.isAssigned do m.assign (mkApp (mkConst ``Exp.var) (shortIdent "%need"))
  g.assign (← mkSorry (← g.getType) false)

def throwNeedUnit {α : Type} (key : Expr) (t : Expr := default) : MetaM α := do
  needUnitRef.set (some key)
  needUnitsAllRef.modify (·.push key)
  cakeLog s!"[need-unit] {((← ppExpr key).pretty.replace "\n" " ").take 200} for term {((← ppExpr t).pretty.replace "\n" " ").take 500}"
  throwError "{needUnitTag}{key}"

/-- A missing global unit: recorded (in a collecting attempt) or an abort. -/
def collectOrThrowNeed (collect : Bool) (g : MVarId) (key t : Expr) : MetaM Unit := do
  if collect || (← collectAllRef.get) then recordNeedUnit g key t else throwNeedUnit key t

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

/-- `closeWith` for a termination goal (a Lean-side fact), run first with the
CakeML-side hypotheses cleared: the values (`Value`, `Exp`, `SemEnv`) bound by
the branches above, and every hypothesis mentioning them (invariants, `Eval`
facts). They cannot matter for termination, but tactics such as `subst_vars`
revert them and grow slow with their number. Falls back to the full context. -/
def closeDec (goal : Expr) (tac : Syntax.Tactic) : MetaM Expr := do
  let cakeTy (ty : Expr) : Bool := ty.find? (fun e => match e with
      | .const n _ => n == ``Value || n == ``Exp || n == ``SemEnv || n == ``Eval || n == ``AppReturns
      | _ => false) |>.isSome
  let goal ← instantiateMVars goal
  let mvar ← mkFreshExprMVar goal
  let cleared? ← observing? do
    let mut cake : FVarIdSet := {}
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if cakeTy ty || ty.hasAnyFVar cake.contains then cake := cake.insert d.fvarId
    if cake.isEmpty || goal.hasAnyFVar cake.contains then throwError "closeDec: nothing to clear"
    let mut g := mvar.mvarId!
    for d in (← getLCtx).decls.toArray.reverse do
      if let some d := d then
        if cake.contains d.fvarId then g ← g.clear d.fvarId
    let remaining ← Tactic.run g (Tactic.evalTactic tac) |>.run'
    unless remaining.isEmpty do throwError "closeDec: side goal"
  if cleared?.isSome then return ← instantiateMVars mvar
  closeWith goal tac

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

/-- `I.rec ps motive minors is major rest…` as `I.casesOn ps motive is major
minors' rest…` when no minor premise uses its induction hypotheses (a single,
non-mutual inductive; the minors must be lambdas over fields and IHs). -/
def recAsCasesOn? (recN : Name) (lvls : List Level) (args : Array Expr) : MetaM (Option Expr) := do
  let some (.recInfo rv) := (← getEnv).find? recN | return none
  unless rv.numMotives == 1 do return none
  let I := recN.getPrefix
  let some (.inductInfo ii) := (← getEnv).find? I | return none
  unless ii.all.length == 1 && !ii.isNested do return none
  let np := rv.numParams; let nm := rv.numMinors; let ni := rv.numIndices
  unless args.size ≥ np + 1 + nm + ni + 1 do return none
  unless (← getEnv).contains (I ++ `casesOn) do return none
  let params := args[:np].toArray
  let mut minors : Array Expr := #[]
  for k in [0:nm] do
    let rule := rv.rules[k]!
    let nf := rule.nfields
    let cty ← instantiateTypeLevelParams (← getConstInfo rule.ctor).toConstantVal (lvls.drop (lvls.length - ii.levelParams.length))
    let cty ← instantiateForall cty params
    let nRec ← forallTelescope cty fun fs _ => do
      let mut c := 0
      for f in fs do
        if (← whnfR (← inferType f)).getAppFn.isConstOf I then c := c + 1
      return c
    -- peel the field and IH binders
    let mut m := args[np + 1 + k]!
    let mut binders : Array (Name × Expr × BinderInfo) := #[]
    for _ in [0:nf + nRec] do
      let .lam n ty b bi := m | return none
      binders := binders.push (n, ty, bi)
      m := b
    if (List.range nRec).any (m.hasLooseBVar ·) then return none
    let mut body := m.lowerLooseBVars nRec nRec
    for (n, ty, bi) in binders[:nf].toArray.reverse do
      body := .lam n ty body bi
    minors := minors.push body
  let motive := args[np]!
  let indices := args[np + 1 + nm : np + 1 + nm + ni].toArray
  let major := args[np + 1 + nm + ni]!
  let rest := args[np + 1 + nm + ni + 1:].toArray
  return some (mkAppN (mkConst (I ++ `casesOn) lvls) (params ++ #[motive] ++ indices ++ #[major] ++ minors ++ rest))

/-- `Eval env (var n) (P x)` for a local whose relation is `P x v`. -/
def evalLocal (env : Expr) (lv : GLVar) (hl : Expr) : MetaM Expr := do
  let rty ← whnfR (← instantiateMVars (← inferType lv.rel))
  let .app P _ := rty | throwError "bad local relation {rty}"
  mkAppOptM ``Eval_var #[env, shortIdent lv.cname, lv.value, P, hl, lv.rel]

-- the solver block compiles past the default limit (LCNF)
set_option maxHeartbeats 1000000 in
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
  -- ghost values: `()`, whatever the term
  let invW ← whnfR inv
  -- the scrutinee of an enclosing match, rebuilt from its fields: its own value
  if !(← get).aliases.isEmpty && t.isApp then
    if let some (_, lv, heq) := (← get).aliases.find? (fun (c, _, _) => c == t) then
      if !lv.lazy then
        let hl ← proveLookupG env lv.cname lv.value (← read).unfoldRec
        let pf ← evalLocal env lv hl
        let pfTy ← inferType pf
        let (``Eval, #[_, ce, pP]) := pfTy.getAppFnArgs | throwError "alias: {pfTy}"
        let .app P major := pP | throwError "alias: {pP}"
        let motive ← withLocalDeclD `x (← inferType major) fun x => do
          mkLambdaFVars #[x] (← mkAppM ``Eval #[env, ce, mkApp P x])
        let pf' ← mkEqNDRec motive pf heq
        if ← isDefEq (← inferType pf') (← g.getType) then
          g.assign pf'
          return
  -- a lazy field (`cake_lazy`): the closure `fun _ : Unit => t`
  if invW.isAppOfArity ``LAZY 2 then
    let lam ← withLocalDeclD `u (mkConst ``Unit) fun u => mkLambdaFVars #[u] t
    let arr ← mkAppM ``Arrow #[mkConst ``UNIT, invW.appArg!]
    return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp arr lam]))
  if invW.isAppOfArity ``GHOST 1 then
    assignProof g (← mkAppOptM ``Eval_ghost #[env, invW.appArg!, t])
    return
  -- monadic computations at a registered state (`MRET`)
  if invW.isAppOf ``MRET then
    if (← get).skipMonadic then modify fun s => { s with skipMonadic := false }
    else if ← solveMonadic g env invW t then return
  let st ← get
  let ctx ← read
  -- a cached field (`cake_cached`): a projection of the stored value
  if let .const f _ := t.getAppFn then
    if t.getAppNumArgs == 1 then
      if let some (d, c) := cachedFieldOf? (← getEnv) f then
        let s := t.appArg!
        let some hc := ctx.hasCons.find? d.name | throwError "no constructor environment for {d.ty}"
        let (_, gs) ← newEvalGoal env (mkApp (mkConst (d.name ++ `cakeInv)) s)
        solve gs
        assignProof g (← mkAppOptM (d.name ++ Name.mkSimple s!"cake_cf{c}")
          #[some env, some hc, none, some s, some (← instantiateMVars (mkMVar gs))])
        return
  -- locals
  if t.isFVar then
    let some lv := st.locals.find? (·.fvar == t) | throwError "unknown local {t}"
    let hl ← proveLookupG env lv.cname lv.value ctx.unfoldRec
    if lv.lazy then
      assignProof g (← mkAppM ``Eval_force #[← evalLocal env lv hl])
    else
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
  -- `List.getLast l h` as `lastD l default` for inhabited types
  if let (``List.getLast, #[α, l, h]) := t.getAppFnArgs then
    if let some dflt ← defaultOf? α then
      let heq ← mkAppOptM ``list_getLast_eq_lastD #[α, l, h, dflt]
      let t' ← mkAppOptM ``lastD #[α, l, dflt]
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
    -- long literals: `s = String.ofByteArray ⟨⟨bytes⟩⟩ _` by `string_lit_eq` (the kernel's
    -- defeq check of the structure-eta form below runs `List.toByteArray`'s quadratic push loop)
    if str.utf8ByteSize > 256 then
      let u8 := mkConst ``UInt8
      let cs := str.toList.map fun c => mkApp (mkConst ``Char.ofNat) (mkRawNatLit c.toNat)
      let csE := cs.foldr (fun c acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Char) c acc)
        (mkApp (mkConst ``List.nil [0]) (mkConst ``Char))
      let bsE ← mkListLit u8 (← str.toUTF8.toList.mapM fun b => mkNumeral u8 b.toNat)
      let hb ← mkEqRefl bsE
      let heq := mkApp3 (mkConst ``string_lit_eq) csE bsE hb
      let t' := mkApp2 (mkConst ``String.ofByteArray)
        (mkApp (mkConst ``ByteArray.mk) (mkApp2 (mkConst ``Array.mk [0]) u8 bsE))
        (mkApp3 (mkConst ``utf8_lit_valid) csE bsE hb)
      let ce ← evalGoalCe g
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv t'])
      solve gb.mvarId!
      let motive ← withLocalDeclD `x (mkConst ``String) fun x => do
        mkLambdaFVars #[x] (← mkAppM ``Eval #[env, ce, mkApp inv x])
      g.assign (← mkEqMP (← mkCongrArg motive (← mkEqSymm heq)) (← instantiateMVars gb))
      return
    let u8 := mkConst ``UInt8
    let bytes ← str.toUTF8.toList.mapM fun b => mkNumeral u8 b.toNat
    let arr ← mkAppOptM ``Array.mk #[u8, ← mkListLit u8 bytes]
    let ba := mkApp (mkConst ``ByteArray.mk) arr
    let t' := mkApp2 (mkConst ``String.ofByteArray) ba (mkApp (mkConst ``String.isValidUTF8) t)
    let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
    return ← solve g'
  -- `UInt64` numerals: `UInt64.ofNat n` (the conversion primitive), not a call of
  -- the generic `OfNat.ofNat` unit with its instance
  if t.isAppOfArity ``OfNat.ofNat 3 && t.appFn!.appFn!.appArg!.isConstOf ``UInt64 then
    if let some n := t.appFn!.appArg!.rawNatLit? then
      let t' := mkApp (mkConst ``UInt64.ofNat) (mkNatLit n)
      return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t']))
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
    if I == ``Array && j == 0 && (← treeArrayElem? (← inferType sExp)).isSome then
      return ← solveArrayToList g env inv sExp
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
  -- (an occurrence in a proposition, e.g. an `if`'s condition `x.1 = true`, is
  -- fine as long as the body typechecks with `x` opaque: substituting would
  -- evaluate the bound value at every use)
  let opaqueOk ← if n == `z then pure true else withLocalDeclD n ty fun x => do
    let b' := b.instantiate1 x
    if !(← occursInProofOrType b' x.fvarId!) then return true
    -- bounded: a failing check can unfold for minutes (e.g. the `UInt32`
    -- arithmetic in `ByteArray.utf8DecodeChar?.assemble₃`); giving up only
    -- means substituting, as before
    tryCatchRuntimeEx
      (withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000 * 1000 }) do
        Core.withCurrHeartbeats do
          withTransparency .instances (Meta.check b')
        return true)
      fun _ => return false
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
  -- integer comparisons: CakeML's `compare`, with `intCmp_spec` as the cast
  let intCmp (op : Name) (sel : Expr → MetaM Expr) (a b : Expr) : GoalM Unit := do
    let (_, ga) ← newEvalGoal env (mkApp (mkConst ``INT) a)
    let (_, gb) ← newEvalGoal env (mkApp (mkConst ``INT) b)
    solve ga; solve gb
    let pf ← mkAppM ``Eval_int_cmp #[mkConst op, ← instantiateMVars (mkMVar ga), ← instantiateMVars (mkMVar gb)]
    let heq ← sel (← mkAppM ``intCmp_spec #[a, b])
    let (``Eval, #[_, ce, _]) := (← inferType pf).getAppFnArgs | throwError "bad integer comparison proof"
    let motive ← withLocalDeclD `x (mkConst ``Bool) fun x => do
      mkLambdaFVars #[x] (← mkAppM ``Eval #[env, ce, mkApp (mkConst ``BOOL) x])
    assignProof g (← mkEqMP (← mkCongrArg motive heq) pf)
  match c.getAppFnArgs with
  | (``LT.lt, #[ty, _, a, b]) =>
    if (← whnfR ty).isConstOf ``Nat then return ← binNat ``Eval_nat_lt a b
    if (← whnfR ty).isConstOf ``Int then
      return ← intCmp ``Flapjack.Opb.lt (fun h => mkAppM ``And.left #[h]) a b
  | (``LE.le, #[ty, _, a, b]) =>
    if (← whnfR ty).isConstOf ``Nat then return ← binNat ``Eval_nat_le a b
    if (← whnfR ty).isConstOf ``Int then
      return ← intCmp ``Flapjack.Opb.leq (fun h => do mkAppM ``And.left #[← mkAppM ``And.right #[h]]) a b
  | (``Eq, #[ty, a, b]) =>
    if (← whnfR ty).isConstOf ``Nat then return ← binNat ``Eval_nat_eq a b
    if (← whnfR ty).isConstOf ``Int then
      let (_, ga) ← newEvalGoal env (mkApp (mkConst ``INT) a)
      let (_, gb) ← newEvalGoal env (mkApp (mkConst ``INT) b)
      solve ga; solve gb
      return ← assignProof g (← mkAppM ``Eval_int_eq #[← instantiateMVars (mkMVar ga), ← instantiateMVars (mkMVar gb)])
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


/-- A list, its spine put in weak head normal form (`conClauses cases`, `xs.map Pat.pvar`). -/
partial def listLitW? (e : Expr) : MetaM (Option (List Expr)) := do
  let e ← whnf (← instantiateMVars e)
  match e.consumeMData.getAppFnArgs with
  | (``List.nil, _) => return some []
  | (``List.cons, #[_, a, rest]) => return (← listLitW? rest).map (a :: ·)
  | _ => return none

/-- The names a pattern binds (`patBindings`), on the translator's pattern terms. -/
partial def patNamesMeta (p : Expr) : MetaM (Option (List String)) := do
  let p ← whnf (← instantiateMVars p)
  match p.consumeMData.getAppFnArgs with
  | (``Pat.pany, _) => return some []
  | (``Pat.plit, _) => return some []
  | (``Pat.pvar, #[n]) => return (mlStringLit? n).map ([·])
  | (``Pat.pref, #[q]) => patNamesMeta q
  | (``Pat.ptannot, #[q, _]) => patNamesMeta q
  | (``Pat.pas, #[q, n]) => do
    let some l ← patNamesMeta q | return none
    return (mlStringLit? n).map (l ++ [·])
  | (``Pat.pcon, #[_, ps]) => do
    let some ps ← listLitW? ps | return none
    let mut acc : List String := []
    for q in ps do
      let some l ← patNamesMeta q | return none
      acc := acc ++ l
    return some acc
  | _ => return none

/-- `pushH h e`, computed (the same code, normalized). -/
partial def pushHMeta (h : String) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let hv ← mkAppM ``Exp.var #[shortIdent h]
  let app := mkApp2 (mkConst ``Exp.app) (mkConst ``Op.opapp) (← mkListLit (mkConst ``Exp) [e, hv])
  match e.consumeMData.getAppFnArgs with
  | (``Exp.fn, #[x, b]) =>
    return mkApp3 (mkConst ``Exp.let_) (← mkAppOptM ``Option.some #[mkConst ``VarN, x]) hv b
  | (``Exp.let_, #[n, e₁, e₂]) =>
    match n.consumeMData.getAppFnArgs with
    | (``Option.none, _) => return mkApp3 (mkConst ``Exp.let_) n e₁ (← pushHMeta h e₂)
    | (``Option.some, #[_, x]) =>
      match mlStringLit? x with
      | some xs => if xs == h then return app else return mkApp3 (mkConst ``Exp.let_) n e₁ (← pushHMeta h e₂)
      | none => throwError "pushH: let name {x}"
    | _ => throwError "pushH: let binder {n}"
  | (``Exp.if_, #[c, a, b]) => return mkApp3 (mkConst ``Exp.if_) c (← pushHMeta h a) (← pushHMeta h b)
  | (``Exp.mat, #[d, pes]) =>
    let some cls ← listLitW? pes | throwError "pushH: clauses {pes}"
    let mut out : Array Expr := #[]
    for cl in cls do
      let (``Prod.mk, #[_, _, p, b]) := (← whnf cl).consumeMData.getAppFnArgs | throwError "pushH: clause {cl}"
      let some names ← patNamesMeta p | throwError "pushH: pattern {p}"
      if names.contains h then return app
      out := out.push (← mkAppM ``Prod.mk #[p, ← pushHMeta h b])
    return mkApp2 (mkConst ``Exp.mat) d (← mkListLit (← mkAppM ``Prod #[mkConst ``Pat, mkConst ``Exp]) out.toList)
  | _ => return app


/-- Close `g` with the `EvalM` lemma `thm`: its variable names fresh, then its
lookups, name disequalities and sub-translations (`Eval` goals, under any
binders of values). -/
partial def applyEvalM (g : MVarId) (thm : Name) (hname : String) (named : List (Name × Expr) := []) : GoalM Unit := do
  let lem ← mkConstWithFreshMVarLevels thm
  let lty ← inferType lem
  let names ← forallTelescope lty fun xs _ => xs.mapM fun x => do return (← x.fvarId!.getDecl).userName
  let (xs, _, concl) ← forallMetaTelescope lty
  -- the state's handle is `h`
  -- and its other variable names are fresh (before unifying: the code goal
  -- lives in a smaller context)
  for (x, n) in xs.zip names do
    if n == `h then x.mvarId!.assign (mlString hname)
    else if (← whnfR (← x.mvarId!.getType)).isConstOf ``Flapjack.Basis.Pure.MlString.MlString then
      x.mvarId!.assign (mlString (← freshCName "t"))
  unless ← isDefEq concl (← g.getType) do
    throwError "applyEvalM: {thm} does not apply: {← instantiateMVars concl}  VS  {← g.getType}"
  -- the given arguments, by name
  for (x, n) in xs.zip names do
    if let some (_, v) := named.find? (·.1 == n) then
      unless ← isDefEq x v do
        throwError "applyEvalM: {thm}: argument {n} := {v} : {← inferType v} does not fit {← inferType x}"
  let gs := xs.map (·.mvarId!)
  -- lookups next (they fix the handle's value)
  for g' in gs do
    if ← g'.isAssigned then continue
    let ty ← instantiateMVars (← g'.getType)
    if let some (_, lhs, _) := ty.eq? then
      let (``nsLookup, #[_, _, _, _, _, ns, id]) := lhs.getAppFnArgs | throwError "applyEvalM: side goal {ty}"
      let (``Ident.short, #[_, _, n]) := id.getAppFnArgs | throwError "applyEvalM: lookup {id}"
      let some n := mlStringLit? (← instantiateMVars n) | throwError "applyEvalM: name {n}"
      let (_, pf) ← lookupNs ns n
      unless ← isDefEq (← inferType pf) ty do throwError "applyEvalM: lookup of {n}: {← inferType pf} vs {ty}"
      g'.assign pf
  for g' in gs do
    if ← g'.isAssigned then continue
    let ty ← instantiateMVars (← g'.getType)
    -- data (code, values) is fixed by the proofs that mention it
    unless ← isProp ty do continue
    let isEvalGoal ← forallTelescope ty fun _ b => do return (← whnfR b).isAppOf ``Eval
    if !isEvalGoal then
      if ty.isAppOf ``HasListCons then
        -- the list constructors, from the translation's context
        unless ← isDefEq (← inferType (← read).hlist) ty do
          throwError "applyEvalM: {thm}: list constructors {ty}"
        g'.assign (← read).hlist
      else
      -- side conditions on literals (disequalities, bounds, distinctness)
      g'.assign (← closeWith ty (← `(tactic| decide)))
    else
      let pf ← forallTelescope ty fun xs body => do
        let gb ← mkFreshExprMVar body
        solve gb.mvarId!
        mkLambdaFVars xs (← instantiateMVars gb)
      g'.assign pf
  for g' in gs do
    unless ← g'.isAssigned do throwError "applyEvalM: {thm}: argument of type {← g'.getType} left unassigned"
  g.assign (← instantiateMVars (mkAppN lem xs))

/-- Run `k` with the state's handle: fresh `b`, `loc`, the environment binding
`hname` to `.loc b loc`, and the handle as a pseudo-local (so that later
lookups through it are proved). Returns `fun b loc => k …`. -/
partial def withHandle (env : Expr) (hname : String)
    (k : Expr → Expr → Expr → GoalM Expr) : GoalM Expr := do
  withLocalDeclD `b (mkConst ``Bool) fun b => do
  withLocalDeclD `loc (mkConst ``Nat) fun loc => do
  withLocalDeclD `hh (mkConst ``Unit) fun hh => do
    let hv ← mkAppM ``Value.loc #[b, loc]
    let env' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsBind #[mlString hname, hv, ← mkAppM ``SemEnv.v #[env]],
      ← mkAppM ``SemEnv.c #[env]]
    let hrel ← mkEqRefl hv
    modify fun s => { s with locals := s.locals.push { fvar := hh, cname := hname, value := hv, rel := hrel } }
    let r ← k env' b loc
    modify fun s => { s with locals := s.locals.pop }
    -- the pseudo-local does not occur in the result
    mkLambdaFVars #[b, loc] r

/-- Monadic computations (`MRET`, a registered state held in a reference): the
methods `bind`, `pure`, `get`, `set`, `throw` and (rewritten) `modify`,
`modifyGet`, each as a function of the state's handle (`Eval_MRET_fn`). -/
partial def solveMonadic (g : MVarId) (env inv t : Expr) : GoalM Bool := do
  let (``MRET, #[σ, ε, _, RF, A, B]) := inv.getAppFnArgs | return false
  -- the units eta-expand over the state argument (`StateT` is a function type):
  -- `fun s => m s` is `m`
  if t.isLambda then
    let b := t.bindingBody!.headBeta
    if let .app f (.bvar 0) := b then
      if !f.hasLooseBVar 0 then
        let t' := f.lowerLooseBVars 1 1
        let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t'])
        solve g'
        return true
  let .const cn _ := t.getAppFn | return false
  let args := t.getAppArgs
  let ce ← evalGoalCe g
  let finish (hname : String) (ceBody pfBody : Expr) : GoalM Bool := do
    unless ← isDefEq ce (← mkAppM ``Exp.fn #[mlString hname, ceBody]) do
      throwError "solveMonadic: code mismatch"
    assignProof g (← mkAppOptM ``Eval_MRET_fn #[none, none, none, RF, A, B, env, mlString hname,
      ceBody, t, pfBody])
    return true
  let hlook (env' : Expr) (hname : String) (hv : Expr) : GoalM Expr := proveLookupG env' hname hv
  -- derived operations: rewrite to `bind`/`get`/`set`/`pure`
  let rewriteBy (heq : Expr) : GoalM Bool := do
    let some (_, _, rhs) := (← inferType heq).eq? | throwError "solveMonadic: bad equation"
    let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv rhs])
    solve gb.mvarId!
    let motive ← withLocalDeclD `x (← inferType t) fun x => do mkLambdaFVars #[x] (← mkAppM ``Eval #[env, ce, mkApp inv x])
    assignProof g (← mkEqMP (← mkCongrArg motive (← mkEqSymm heq)) (← instantiateMVars gb))
    return true
  -- array states (`arrRel`): read with a default, write in place
  -- state records (`recRel`): a field's map operation is the table operation on
  -- the field's table (`EvalM_lens`); the plain part is read (`EvalM_plain`)
  let isRec := RF.isLambda && RF.bindingBody!.getAppFn.isConstOf ``ConPastel.Translator.recRel
  let recOps := [``ConPastel.Translator.hmFind, ``ConPastel.Translator.hmInsertD,
    ``ConPastel.Translator.hmSize, ``ConPastel.Translator.hmClear, ``ConPastel.Translator.stRead,
    ``ConPastel.Translator.swapRun]
  if isRec && recOps.contains cn then
    let (``ConPastel.Translator.recRel, #[σr, tabsE, plainE, _]) := RF.bindingBody!.getAppFnArgs
      | throwError "record state: {RF}"
    let .const tabsN _ := tabsE | throwError "record state: tables {tabsE}"
    let some (_, info) := (stateRecExt.getState (← getEnv)).toList.find? (·.2.tabs == tabsN)
      | throwError "record state: unregistered {tabsN}"
    let N := info.accs.size
    let hname ← freshCName "h"
    let codeOf (pf : Expr) : GoalM Expr := do
      forallTelescope (← inferType pf) fun _ body => do
        let body ← whnfR body
        unless body.isAppOf ``EvalM do throwError "record state: proof {body}"
        instantiateMVars (body.getArg! 5)
    if cn == ``ConPastel.Translator.swapRun then
      let ps := info.swap
      if ps.isEmpty then throwError "record state: no swap registered for {σr}"
      let m := ps.size
      let enter := args[3]!
      let leave := args[4]!
      let x := args[5]!
      let snames ← (List.range m).mapM fun _ => freshCName "s"
      let fnames ← (List.range m).mapM fun _ => freshCName "f"
      -- the entries of the swapped-in empty tables
      let entKVB ← withLocalDeclD `st σr fun st => do
        let some tl ← unfoldDefinition? (mkApp tabsE st) | throwError "swap: tables"
        let some es := listLit? tl.headBeta | throwError "swap: tables {tl}"
        es.toArray.mapM fun e => do
          let (``ConPastel.Translator.TEntry.mk, #[K, V, BI, _]) := e.getAppFnArgs | throwError "swap: entry {e}"
          pure (K, V, BI)
      let entTy := mkConst ``ConPastel.Translator.TEntry
      let nsTy ← mkAppM ``Namespace #[mkConst ``ModN, mkConst ``VarN, mkConst ``Value]
      let mut emps : Array Expr := #[]
      let mut raws : Array Expr := #[]
      let mut nils : Array (Expr × Expr) := #[]
      for (_, j) in ps do
        let (K, V, BI) := entKVB[j]!
        let instB ← synthInstance (← mkAppM ``BEq #[K])
        let instH ← synthInstance (← mkAppM ``Hashable #[K])
        let hmTy := mkAppN (mkConst ``Std.HashMap [levelZero, levelZero]) #[K, V, instB, instH]
        let emp ← mkAppOptM ``EmptyCollection.emptyCollection #[hmTy, none]
        let raw ← mkAppM ``Std.DHashMap.inner #[← mkAppM ``Std.HashMap.inner #[emp]]
        emps := emps.push (mkAppN (mkConst ``ConPastel.Translator.TEntry.mk) #[K, V, BI, raw])
        raws := raws.push (← mkAppOptM ``ConPastel.Translator.emptyRaw_empty #[K, V, instB, instH])
        let nil := mkApp2 (mkConst ``Std.DHashMap.Internal.AssocList.nil [levelZero, levelZero]) K
          (← withLocalDeclD `x K fun x => mkLambdaFVars #[x] V)
        let cn ← mkFreshExprMVar (mkConst ``Exp)
        let pn ← withLocalDeclD `ns nsTy fun ns => do
          let env' ← mkAppM ``SemEnv.mk #[ns, ← mkAppM ``SemEnv.c #[env]]
          let gn ← mkFreshExprMVar (← mkAppM ``Eval #[env', cn, mkApp BI nil])
          solve gn.mvarId!
          mkLambdaFVars #[ns] (← instantiateMVars gn)
        nils := nils.push (← instantiateMVars cn, pn)
      let empE ← mkListLit entTy emps.toList
      let mut hemp ← mkAppOptM ``ConPastel.Translator.emptyRaws_nil #[]
      for (e, pr) in (emps.toList.zip raws.toList).reverse do
        hemp ← mkAppOptM ``ConPastel.Translator.emptyRaws_cons #[e, none, pr, hemp]
      let hname ← freshCName "h"
      let psE ← mkListLit (← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat])
        (← ps.toList.mapM fun (i, j) => mkAppM ``Prod.mk #[toExpr i, toExpr j])
      let snamesE ← mkListLit (mkConst ``VarN) (snames.map mlString)
      let fnamesE ← mkListLit (mkConst ``VarN) (fnames.map mlString)
      let enilsE ← mkListLit (mkConst ``Exp) (nils.toList.map (·.1))
      let pf ← withHandle env hname fun env' b loc => do
        let R := (mkApp RF loc).headBeta
        let hv ← mkAppM ``Value.loc #[b, loc]
        -- the nil codes, as `Forall₂`
        let Rn ← withLocalDeclD `e (mkConst ``Exp) fun e => withLocalDeclD `t entTy fun t => do
          let body ← withLocalDeclD `ns nsTy fun ns => do
            let env'' ← mkAppM ``SemEnv.mk #[ns, ← mkAppM ``SemEnv.c #[env']]
            let tK ← mkAppM ``ConPastel.Translator.TEntry.K #[t]
            let tV ← mkAppM ``ConPastel.Translator.TEntry.V #[t]
            let nil := mkApp2 (mkConst ``Std.DHashMap.Internal.AssocList.nil [levelZero, levelZero]) tK
              (← withLocalDeclD `x tK fun x => mkLambdaFVars #[x] tV)
            mkForallFVars #[ns] (← mkAppM ``Eval #[env'', e, mkApp (← mkAppM ``ConPastel.Translator.TEntry.BI #[t]) nil])
          mkLambdaFVars #[e, t] body
        let mut hnil ← mkAppOptM ``List.Forall₂.nil #[mkConst ``Exp, entTy, Rn]
        let mut esL : List Expr := []
        let mut tsL : List Expr := []
        for ((cn, pn), e) in (nils.toList.zip emps.toList).reverse do
          hnil ← mkAppOptM ``List.Forall₂.cons #[mkConst ``Exp, entTy, Rn, cn, e, ← mkListLit (mkConst ``Exp) esL,
            ← mkListLit entTy tsL, pn, hnil]
          esL := cn :: esL
          tsL := e :: tsL
        -- the computation, under the swap's variables
        let finTy ← mkArrow (mkApp (mkConst ``Fin) (toExpr m)) (mkConst ``Value)
        let cx ← mkFreshExprMVar (mkConst ``Exp)
        let hx ← withLocalDeclD `vs finTy fun vs => withLocalDeclD `ws finTy fun ws => do
          let mut envX := env'
          for k in [0:m] do
            let fk ← mkAppM ``Fin.mk #[toExpr k, ← mkDecideProof (← mkLt (toExpr k) (toExpr m))]
            envX ← mkAppM ``SemEnv.mk #[← mkAppM ``nsOptBind #[← mkAppM ``Option.some #[mlString snames[k]!],
              mkApp vs fk, ← mkAppM ``SemEnv.v #[envX]], ← mkAppM ``SemEnv.c #[envX]]
          for k in [0:m] do
            let fk ← mkAppM ``Fin.mk #[toExpr k, ← mkDecideProof (← mkLt (toExpr k) (toExpr m))]
            envX ← mkAppM ``SemEnv.mk #[← mkAppM ``nsOptBind #[← mkAppM ``Option.some #[mlString fnames[k]!],
              mkApp ws fk, ← mkAppM ``SemEnv.v #[envX]], ← mkAppM ``SemEnv.c #[envX]]
          let gx ← mkFreshExprMVar (← mkAppM ``Eval #[envX, cx, mkApp inv x])
          solve gx.mvarId!
          let hlx ← proveLookupG envX hname hv
          let run ← mkAppOptM ``EvalM_runPush #[none, none, none, RF, A, B, envX, ← instantiateMVars cx,
            mlString hname, b, loc, x, hlx, ← instantiateMVars gx]
          mkLambdaFVars #[vs, ws] run
        let goal ← mkAppM ``EvalM #[R, env', ← mkFreshExprMVar (mkConst ``Exp), A, B, t]
        let gm ← mkFreshExprMVar goal
        let hN ← withLocalDeclD `st σr fun st => do mkLambdaFVars #[st] (← mkEqRefl (toExpr N))
        let hE ← withLocalDeclD `st σr fun st => do mkLambdaFVars #[st] (← mkEqRefl (mkApp tabsE (mkApp enter st)))
        let hL ← withLocalDeclD `st σr fun st => withLocalDeclD `st₂ σr fun st₂ => do
          mkLambdaFVars #[st, st₂] (← mkEqRefl (mkApp tabsE (mkApp2 leave st₂ st)))
        let P1 ← withLocalDeclD `st σr fun st => withLocalDeclD `v (mkConst ``Value) fun v => do
          mkLambdaFVars #[st, v] (← mkAppM ``Iff.refl #[mkApp2 plainE (mkApp enter st) v])
        let P2 ← withLocalDeclD `st σr fun st => withLocalDeclD `st₂ σr fun st₂ =>
          withLocalDeclD `v (mkConst ``Value) fun v => do
            mkLambdaFVars #[st, st₂, v] (← mkAppM ``Iff.refl #[mkApp2 plainE (mkApp2 leave st₂ st) v])
        let mlen (l : Expr) : GoalM Expr := do mkEqRefl (← mkAppM ``List.length #[l])
        applyEvalM gm.mvarId! ``ConPastel.Translator.EvalM_swapL hname
          [(`N, toExpr N), (`ps, psE), (`snames, snamesE), (`fnames, fnamesE), (`enils, enilsE),
           (`emp, empE), (`enter, enter), (`leave, leave), (`x, x),
           (`hN, hN), (`hls, ← mlen snamesE), (`hlf, ← mlen fnamesE), (`hle, ← mlen enilsE),
           (`hlemp, ← mlen empE), (`hemp, hemp), (`hnil, hnil), (`hE, hE), (`hL, hL), (`P1, P1), (`P2, P2),
           (`hx, hx)]
        instantiateMVars gm
      return ← finish hname (← codeOf pf) pf
    if cn == ``ConPastel.Translator.stRead then
      let f := args.back!
      unless ← isDefEq f (mkConst info.plainAcc) do throwError "record state: {f} is not the plain part"
      let pf ← withHandle env hname fun env' _ loc => do
        let goal ← mkAppM ``EvalM #[(mkApp RF loc).headBeta, env', ← mkFreshExprMVar (mkConst ``Exp), A, B, t]
        let gm ← mkFreshExprMVar goal
        let hlen ← withLocalDeclD `st σr fun st => do mkLambdaFVars #[st] (← mkEqRefl (toExpr N))
        let hA ← withLocalDeclD `st σr fun st => withLocalDeclD `v (mkConst ``Value) fun v =>
          withLocalDeclD `hp (mkApp2 plainE st v) fun hp => mkLambdaFVars #[st, v, hp] hp
        applyEvalM gm.mvarId! ``ConPastel.Translator.EvalM_plain hname
          [(`n, toExpr N), (`f, f), (`hlen, hlen), (`hA, hA)]
        instantiateMVars gm
      return ← finish hname (← codeOf pf) pf
    let K := args[2]!
    let V := args[3]!
    let instB := args[4]!
    let instH := args[5]!
    let ε := args[1]!
    let get := if cn == ``ConPastel.Translator.hmFind then args[args.size - 2]!
      else if cn == ``ConPastel.Translator.hmInsertD then args[args.size - 4]!
      else if cn == ``ConPastel.Translator.hmSize then args.back!
      else args[args.size - 2]!
    let mut idx? : Option Nat := none
    for j in [0:N] do
      if idx?.isNone then
        if ← isDefEq get (mkConst info.accs[j]!) then idx? := some j
    let some i := idx? | throwError "record state: {get} is not a field of {σr}"
    let bkt := mkApp2 (mkConst ``Std.DHashMap.Internal.AssocList [levelZero, levelZero]) K
      (← withLocalDeclD `x K fun x => mkLambdaFVars #[x] V)
    let BI ← invOf bkt
    let getR ← withLocalDeclD `st σr fun st => do
      mkLambdaFVars #[st] (← mkAppM ``Std.DHashMap.inner #[← mkAppM ``Std.HashMap.inner #[mkApp get st]])
    let hlen ← withLocalDeclD `st σr fun st => do
      mkLambdaFVars #[st] (← mkDecideProof (← mkLt (toExpr i) (toExpr N)))
    let hent ← withLocalDeclD `st σr fun st => do
      mkLambdaFVars #[st] (← mkEqRefl (mkAppN (mkConst ``ConPastel.Translator.TEntry.mk) #[K, V, BI, (mkApp getR st).headBeta]))
    let hsim ← match cn with
      | ``ConPastel.Translator.hmFind =>
        mkAppOptM ``ConPastel.Translator.sim_find #[σr, ε, tabsE, plainE, toExpr i, K, V, instB, instH, BI, get,
          hlen, hent, args.back!]
      | ``ConPastel.Translator.hmSize =>
        mkAppOptM ``ConPastel.Translator.sim_size #[σr, ε, tabsE, plainE, toExpr i, K, V, instB, instH, BI, get,
          hlen, hent]
      | ``ConPastel.Translator.hmInsertD => do
        let set := args[args.size - 3]!
        let htabs ← withLocalDeclD `st σr fun st => do
          let mty ← inferType (mkApp get st)
          withLocalDeclD `m mty fun m => do
            let emp ← mkAppOptM ``EmptyCollection.emptyCollection #[mty, none]
            mkLambdaFVars #[st, m] (← mkEqRefl (mkApp tabsE (mkApp2 set (mkApp2 set st emp) m)))
        let hP ← withLocalDeclD `st σr fun st => do
          let mty ← inferType (mkApp get st)
          withLocalDeclD `m mty fun m => withLocalDeclD `v (mkConst ``Value) fun v => do
            mkLambdaFVars #[st, m, v] (← mkAppM ``Iff.refl #[mkApp2 plainE st v])
        mkAppOptM ``ConPastel.Translator.sim_insert #[σr, ε, tabsE, plainE, toExpr i, K, V, instB, instH, BI, get,
          set, htabs, hP, args[args.size - 2]!, args.back!]
      | _ => do
        let set := args.back!
        let htabs ← withLocalDeclD `st σr fun st => do
          let mty ← inferType (mkApp get st)
          withLocalDeclD `m mty fun m => do
            mkLambdaFVars #[st, m] (← mkEqRefl (mkApp tabsE (mkApp2 set st m)))
        let hP ← withLocalDeclD `st σr fun st => do
          let mty ← inferType (mkApp get st)
          withLocalDeclD `m mty fun m => withLocalDeclD `v (mkConst ``Value) fun v => do
            mkLambdaFVars #[st, m, v] (← mkAppM ``Iff.refl #[mkApp2 plainE st v])
        mkAppOptM ``ConPastel.Translator.sim_clear #[σr, ε, tabsE, plainE, toExpr i, K, V, instB, instH, BI, get,
          set, htabs, hP]
    let pf ← withHandle env hname fun env' _ loc => do
      let goal ← mkAppM ``EvalM #[(mkApp RF loc).headBeta, env', ← mkFreshExprMVar (mkConst ``Exp), A, B, t]
      let gm ← mkFreshExprMVar goal
      applyEvalM gm.mvarId! ``ConPastel.Translator.EvalM_lens hname
        [(`i, toExpr i), (`K, K), (`V, V), (`BI, BI), (`getR, getR), (`hlen, hlen), (`hent, hent),
         (`hsim, hsim)]
      instantiateMVars gm
    return ← finish hname (← codeOf pf) pf
  -- hash-table states (`tblRel`): the table primitives, each by its `EvalM` lemma
  let isTbl := RF.isLambda && RF.bindingBody!.getAppFn.isConstOf ``ConPastel.Translator.tblRel
  let tblPrims := [(``ConPastel.Translator.tNB, ``ConPastel.Translator.EvalM_tNB),
    (``ConPastel.Translator.tSize, ``ConPastel.Translator.EvalM_tSize),
    (``ConPastel.Translator.tGetB, ``ConPastel.Translator.EvalM_tGetB),
    (``ConPastel.Translator.tSetB, ``ConPastel.Translator.EvalM_tSetB),
    (``ConPastel.Translator.tSetSize, ``ConPastel.Translator.EvalM_tSetSize),
    (``ConPastel.Translator.tRealloc, ``ConPastel.Translator.EvalM_tRealloc),
    (``ConPastel.Translator.tReadAll, ``ConPastel.Translator.EvalM_tReadAll)]
  if isTbl then
    if let some (_, thm) := tblPrims.find? (·.1 == cn) then
      let hname ← freshCName "h"
      let ceBody ← mkFreshExprMVar (mkConst ``Exp)
      let pf ← withHandle env hname fun env' _ loc => do
        let goal ← mkAppM ``EvalM #[(mkApp RF loc).headBeta, env', ceBody, A, B, t]
        let gm ← mkFreshExprMVar goal
        applyEvalM gm.mvarId! thm hname
        instantiateMVars gm
      return ← finish hname (← instantiateMVars ceBody) pf
  let isArr := (RF.headBeta.getAppFn.isLambda && (RF.bindingBody!.getAppFn.isConstOf ``ConPastel.Translator.arrRel))
  if isArr && (cn == ``ConPastel.Translator.getsD || cn == ``ConPastel.Translator.setM) then
    let (``arrRel, #[_, Ael, _]) := RF.bindingBody!.getAppFnArgs | throwError "array state: relation {RF}"
    let hname ← freshCName "h"
    let ixname ← freshCName "i"
    let xvname ← freshCName "y"
    let ne (a b : String) : GoalM Expr := do
      let goal := mkNot (← mkEq (mlString a) (mlString b))
      closeWith goal (← `(tactic| decide))
    let ci ← mkFreshExprMVar (mkConst ``Exp)
    let ce₂ ← mkFreshExprMVar (mkConst ``Exp)
    let pf ← withHandle env hname fun env' b loc => do
      let hv ← mkAppM ``Value.loc #[b, loc]
      let hl ← proveLookupG env' hname hv
      let gi ← mkFreshExprMVar (← mkAppM ``Eval #[env', ci, mkApp (mkConst ``NAT) args[2]!])
      solve gi.mvarId!
      let h₂ ← withLocalDeclD `v (mkConst ``Value) fun v => do
        let env'' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsOptBind #[← mkAppM ``Option.some #[mlString ixname], v,
          ← mkAppM ``SemEnv.v #[env']], ← mkAppM ``SemEnv.c #[env']]
        let g₂ ← mkFreshExprMVar (← mkAppM ``Eval #[env'', ce₂, mkApp Ael args[3]!])
        solve g₂.mvarId!
        mkLambdaFVars #[v] (← instantiateMVars g₂)
      if cn == ``ConPastel.Translator.getsD then
        mkAppOptM ``EvalM_getsD #[none, none, Ael, B, env', mlString hname, mlString ixname, ← instantiateMVars ci,
          ← instantiateMVars ce₂, args[2]!, args[3]!, b, loc, hl, ← ne ixname hname, ← instantiateMVars gi, h₂]
      else
        mkAppOptM ``EvalM_setM #[none, none, Ael, B, env', mlString hname, mlString ixname, mlString xvname,
          ← instantiateMVars ci, ← instantiateMVars ce₂, args[2]!, args[3]!, b, loc, hl, ← ne ixname hname,
          ← ne xvname hname, ← ne xvname ixname, ← instantiateMVars gi, h₂]
    let hId := mkApp (mkConst ``Exp.var) (shortIdent hname)
    let ixId := mkApp (mkConst ``Exp.var) (shortIdent ixname)
    let lt ← mkAppM ``ltLen #[shortIdent ixname, shortIdent hname]
    let body ← if cn == ``ConPastel.Translator.getsD then
        mkAppM ``Exp.let_ #[← mkAppM ``Option.some #[mlString ixname], ← instantiateMVars ci,
          ← mkAppM ``Exp.if_ #[lt, ← mkAppM ``Exp.app #[mkConst ``Op.asub, ← mkListLit (mkConst ``Exp) [hId, ixId]],
            ← instantiateMVars ce₂]]
      else do
        let xId := mkApp (mkConst ``Exp.var) (shortIdent xvname)
        let unitE := mkConst ``unitExp
        mkAppM ``Exp.let_ #[← mkAppM ``Option.some #[mlString ixname], ← instantiateMVars ci,
          ← mkAppM ``Exp.let_ #[← mkAppM ``Option.some #[mlString xvname], ← instantiateMVars ce₂,
            ← mkAppM ``Exp.if_ #[lt, ← mkAppM ``Exp.app #[mkConst ``Op.aupdate, ← mkListLit (mkConst ``Exp) [hId, ixId, xId]],
              unitE]]]
    return ← finish hname body pf
  if cn == ``modify && args.size == 4 then
    return ← rewriteBy (← mkAppOptM ``modify_eq_bind #[σ, ε, args[3]!])
  if cn == ``modifyGet && args.size == 5 then
    return ← rewriteBy (← mkAppOptM ``modifyGet_eq_bind #[σ, ε, none, args[4]!])
  if cn == ``Bind.bind && args.size == 6 then
    let α := args[2]!
    let x := args[4]!
    let f := args[5]!
    let invA' ← invOf α
    let hname ← freshCName "h"
    let aname ← freshCName "a"
    let ceBody ← mkFreshExprMVar (mkConst ``Exp)
    let pf ← withHandle env hname fun env' b loc => do
      let hv ← mkAppM ``Value.loc #[b, loc]
      let invX ← mkAppOptM ``MRET #[σ, ε, α, RF, invA', B]
      let (cex, gx) ← newEvalGoal env' (mkApp invX x)
      solve gx
      let pfx ← instantiateMVars (mkMVar gx)
      let hl₁ ← hlook env' hname hv
      let runX ← mkAppOptM ``EvalM_runPush #[none, none, none, RF, invA', B, env', cex,
        mlString hname, b, loc, x, hl₁, pfx]
      let cef ← mkFreshExprMVar (mkConst ``Exp)
      let cont ← withLocalDeclD `a α fun a => do
        withLocalDeclD `av (mkConst ``Value) fun av => do
        withLocalDeclD `hA (mkApp2 invA' a av) fun hA => do
          let env'' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsOptBind #[← mkAppM ``Option.some #[mlString aname], av,
            ← mkAppM ``SemEnv.v #[env']], ← mkAppM ``SemEnv.c #[env']]
          modify fun s => { s with locals := s.locals.push { fvar := a, cname := aname, value := av, rel := hA } }
          let fa := (mkApp f a).headBeta
          let gf ← mkFreshExprMVar (← mkAppM ``Eval #[env'', cef, mkApp inv fa])
          solve gf.mvarId!
          modify fun s => { s with locals := s.locals.pop }
          let hl₂ ← hlook env'' hname hv
          let runF ← mkAppOptM ``EvalM_runPush #[none, none, none, RF, A, B, env'', cef,
            mlString hname, b, loc, fa, hl₂, ← instantiateMVars gf]
          mkLambdaFVars #[a, av, hA] runF
      let body ← mkAppM ``Exp.let_ #[← mkAppM ``Option.some #[mlString aname],
        ← pushHMeta hname cex, ← pushHMeta hname (← instantiateMVars cef)]
      unless ← isDefEq ceBody body do throwError "solveMonadic: bind body"
      mkAppOptM ``EvalM_bind #[none, none, none, none, none, env', mlString aname, none, none, invA', A, B,
        x, f, runX, cont]
    return ← finish hname (← instantiateMVars ceBody) pf
  if cn == ``Pure.pure && args.size == 4 then
    let a := args[3]!
    let hname ← freshCName "h"
    let ceBody ← mkFreshExprMVar (mkConst ``Exp)
    let pf ← withHandle env hname fun env' _ loc => do
      let ga ← mkFreshExprMVar (← mkAppM ``Eval #[env', ceBody, mkApp A a])
      solve ga.mvarId!
      mkAppOptM ``EvalM_pure #[none, none, none, (mkApp RF loc).headBeta, env', ceBody, A, B, a,
        ← instantiateMVars ga]
    return ← finish hname (← instantiateMVars ceBody) pf
  if cn == ``MonadState.get && args.size == 3 then
    let hname ← freshCName "h"
    let S ← invOf σ
    let pf ← withHandle env hname fun env' b loc => do
      let hv ← mkAppM ``Value.loc #[b, loc]
      mkAppOptM ``EvalM_get #[none, none, S, loc, env', shortIdent hname, B, b,
        ← hlook env' hname hv]
    let body ← mkAppM ``Exp.app #[mkConst ``Op.opderef, ← mkListLit (mkConst ``Exp)
      [← mkAppM ``Exp.var #[shortIdent hname]]]
    return ← finish hname body pf
  if cn == ``MonadStateOf.set && args.size == 4 then
    let st' := args[3]!
    let hname ← freshCName "h"
    let S ← invOf σ
    let cs ← mkFreshExprMVar (mkConst ``Exp)
    let pf ← withHandle env hname fun env' b loc => do
      let hv ← mkAppM ``Value.loc #[b, loc]
      let gs ← mkFreshExprMVar (← mkAppM ``Eval #[env', cs, mkApp S st'])
      solve gs.mvarId!
      mkAppOptM ``EvalM_set #[none, none, S, loc, env', shortIdent hname, cs, B, b, st',
        ← hlook env' hname hv, ← instantiateMVars gs]
    let body ← mkAppM ``Exp.app #[mkConst ``Op.opassign, ← mkListLit (mkConst ``Exp)
      [← mkAppM ``Exp.var #[shortIdent hname], ← instantiateMVars cs]]
    return ← finish hname body pf
  if cn == ``MonadExcept.throw && args.size == 5 then
    let e := args[4]!
    let hname ← freshCName "h"
    let ceE ← mkFreshExprMVar (mkConst ``Exp)
    let pf ← withHandle env hname fun env' _ loc => do
      let ge ← mkFreshExprMVar (← mkAppM ``Eval #[env', ceE, mkApp B e])
      solve ge.mvarId!
      mkAppOptM ``EvalM_throw #[none, none, none, (mkApp RF loc).headBeta, env', ceE, A, B, e,
        ← instantiateMVars ge]
    return ← finish hname (← mkAppM ``Exp.raise #[← instantiateMVars ceE]) pf
  -- control (`match`, `if`, `let`, recursor): solved as a plain value, the
  -- application to the handle pushed into its branches (`EvalM_runPush`)
  let isControl : GoalM Bool := do
    if t.isLet then return true
    let .const c _ := t.getAppFn | return false
    return c == ``ite || c == ``dite || c == ``cond || (← Meta.isMatcher c) ||
      isCasesOnRecursor (← getEnv) c || isRecCore (← getEnv) c
  if ← isControl then
    let hname ← freshCName "h"
    let ce' ← mkFreshExprMVar (mkConst ``Exp)
    let pf ← withHandle env hname fun env' b loc => do
      let hv ← mkAppM ``Value.loc #[b, loc]
      let hl ← hlook env' hname hv
      let gp ← mkFreshExprMVar (← mkAppM ``Eval #[env', ce', mkApp inv t])
      modify fun s => { s with skipMonadic := true }
      solve gp.mvarId!
      mkAppOptM ``EvalM_runPush #[none, none, none, RF, A, B, env', ce', mlString hname, b, loc, t, hl,
        ← instantiateMVars gp]
    return ← finish hname (← pushHMeta hname (← instantiateMVars ce')) pf
  return false

/-- `runRef init m` at a registered state: `m` on a fresh reference holding
`init`, its value or (by `handle`) its exception made an `Except` (`Eval_runRef`). -/
partial def solveRunRef (g : MVarId) (env inv : Expr) (args : Array Expr) : GoalM Unit := do
  let #[σ, ε, α, init, m] := args | throwError "runRef: arguments"
  let S ← invOf σ
  let A ← invOf α
  let B ← invOf ε
  let hname ← freshCName "h"
  let xname ← freshCName "x"
  let yname ← freshCName "y"
  let ce ← evalGoalCe g
  let ci ← mkFreshExprMVar (mkConst ``Exp)
  let gi ← mkFreshExprMVar (← mkAppM ``Eval #[env, ci, mkApp S init])
  solve gi.mvarId!
  let envH (b loc : Expr) : GoalM Expr := do
    mkAppM ``SemEnv.mk #[← mkAppM ``nsOptBind #[← mkAppM ``Option.some #[mlString hname],
      ← mkAppM ``Value.loc #[b, loc], ← mkAppM ``SemEnv.v #[env]], ← mkAppM ``SemEnv.c #[env]]
  let rf ← withLocalDeclD `loc (mkConst ``Nat) fun loc => do
    mkLambdaFVars #[loc] (← mkAppM ``ConPastel.Translator.refRel #[S, loc])
  let invM ← mkAppOptM ``MRET #[σ, ε, α, rf, A, B]
  let cm ← mkFreshExprMVar (mkConst ``Exp)
  let hm ← withLocalDeclD `b (mkConst ``Bool) fun b => do
    withLocalDeclD `loc (mkConst ``Nat) fun loc => do
      let env' ← envH b loc
      let gm ← mkFreshExprMVar (← mkAppM ``Eval #[env', cm, mkApp invM m])
      solve gm.mvarId!
      mkLambdaFVars #[b, loc] (← instantiateMVars gm)
  let okF ← mkAppOptM ``Except.ok #[ε, α]
  let errF ← mkAppOptM ``Except.error #[ε, α]
  let cok ← mkFreshExprMVar (mkConst ``Exp)
  let hok ← withLocalDeclD `b (mkConst ``Bool) fun b => do
    withLocalDeclD `loc (mkConst ``Nat) fun loc => do
    withLocalDeclD `a α fun a => do
    withLocalDeclD `av (mkConst ``Value) fun av => do
    withLocalDeclD `hA (mkApp2 A a av) fun hA => do
      let env' ← envH b loc
      let env'' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsOptBind #[← mkAppM ``Option.some #[mlString xname], av,
        ← mkAppM ``SemEnv.v #[env']], ← mkAppM ``SemEnv.c #[env]]
      modify fun s => { s with locals := s.locals.push { fvar := a, cname := xname, value := av, rel := hA } }
      let gk ← mkFreshExprMVar (← mkAppM ``Eval #[env'', cok, mkApp inv (mkApp okF a)])
      solve gk.mvarId!
      modify fun s => { s with locals := s.locals.pop }
      mkLambdaFVars #[b, loc, a, av, hA] (← instantiateMVars gk)
  let cerr ← mkFreshExprMVar (mkConst ``Exp)
  let herr ← withLocalDeclD `b (mkConst ``Bool) fun b => do
    withLocalDeclD `loc (mkConst ``Nat) fun loc => do
    withLocalDeclD `e ε fun e => do
    withLocalDeclD `ev (mkConst ``Value) fun ev => do
    withLocalDeclD `hB (mkApp2 B e ev) fun hB => do
      let env' ← envH b loc
      let pty ← mkAppM ``Prod #[mkConst ``VarN, mkConst ``Value]
      let al ← mkListLit pty [← mkAppM ``Prod.mk #[mlString yname, ev]]
      let env'' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsAppend #[← mkAppOptM ``alistToNs #[mkConst ``ModN, none, none, al],
        ← mkAppM ``SemEnv.v #[env']], ← mkAppM ``SemEnv.c #[env]]
      modify fun s => { s with locals := s.locals.push { fvar := e, cname := yname, value := ev, rel := hB } }
      let gk ← mkFreshExprMVar (← mkAppM ``Eval #[env'', cerr, mkApp inv (mkApp errF e)])
      solve gk.mvarId!
      modify fun s => { s with locals := s.locals.pop }
      mkLambdaFVars #[b, loc, e, ev, hB] (← instantiateMVars gk)
  let pf ← mkAppOptM ``Eval_runRef #[σ, ε, α, none, S, A, B, inv, env, ← instantiateMVars ci,
    ← instantiateMVars cm, ← instantiateMVars cok, ← instantiateMVars cerr, mlString hname, mlString xname,
    mlString yname, init, m, okF, errF, ← instantiateMVars gi, hm, hok, herr]
  let pty ← inferType pf
  let some (_, ceP, _) := (← whnfR pty).getAppFnArgs.2.toList.toArray[1]? |>.map (fun c => ((), c, ())) | throwError "runRef: proof"
  unless ← isDefEq ce ceP do throwError "runRef: code mismatch"
  assignProof g pf

/-- `runRef init m` at a registered state record: `m` on a freshly allocated
record of empty tables (`Eval_runState`, `initRec_ok'`). -/
partial def solveRunRec (g : MVarId) (env inv : Expr) (args : Array Expr) (info : StateRecInfo) : GoalM Unit := do
  let #[σ, ε, α, init, m] := args | throwError "runRef: arguments"
  let A ← invOf α
  let B ← invOf ε
  let hname ← freshCName "h"
  let xname ← freshCName "x"
  let yname ← freshCName "y"
  let stname ← freshCName "s"
  let aname ← freshCName "a"
  let ce ← evalGoalCe g
  let tabsE := mkConst info.tabs
  let plainE := mkConst info.plain
  -- the tables of `init`, entry by entry
  let some tl ← unfoldDefinition? (mkApp tabsE init) | throwError "runRef: tables"
  let some ents := listLit? tl.headBeta | throwError "runRef: tables {tl}"
  let nsTy ← mkAppM ``Namespace #[mkConst ``ModN, mkConst ``VarN, mkConst ``Value]
  let mut nils : Array (Expr × Expr) := #[]
  let mut raws : Array Expr := #[]
  for e in ents do
    let (``ConPastel.Translator.TEntry.mk, #[K, V, BI, _]) := e.getAppFnArgs | throwError "runRef: entry {e}"
    let nil := mkApp2 (mkConst ``Std.DHashMap.Internal.AssocList.nil [levelZero, levelZero]) K
      (← withLocalDeclD `x K fun x => mkLambdaFVars #[x] V)
    let cn ← mkFreshExprMVar (mkConst ``Exp)
    let pn ← withLocalDeclD `ns nsTy fun ns => do
      let env' ← mkAppM ``SemEnv.mk #[ns, ← mkAppM ``SemEnv.c #[env]]
      let gn ← mkFreshExprMVar (← mkAppM ``Eval #[env', cn, mkApp BI nil])
      solve gn.mvarId!
      mkLambdaFVars #[ns] (← instantiateMVars gn)
    nils := nils.push (← instantiateMVars cn, pn)
    let instB ← synthInstance (← mkAppM ``BEq #[K])
    let instH ← synthInstance (← mkAppM ``Hashable #[K])
    raws := raws.push (← mkAppOptM ``ConPastel.Translator.emptyRaw_empty #[K, V, instB, instH])
  -- `∀ e ∈ tabs init, EmptyRaw e.raw`
  let mut hraw ← mkAppOptM ``ConPastel.Translator.emptyRaws_nil #[]
  for (e, pr) in (ents.zip raws.toList).reverse do
    hraw ← mkAppOptM ``ConPastel.Translator.emptyRaws_cons #[e, none, pr, hraw]
  -- `Forall₂ (fun e t => ∀ ns, Eval {v := ns, c := env.c} e (t.BI nil)) enils (tabs init)`
  let R ← withLocalDeclD `e (mkConst ``Exp) fun e => withLocalDeclD `t (mkConst ``ConPastel.Translator.TEntry) fun t => do
    let body ← withLocalDeclD `ns nsTy fun ns => do
      let env' ← mkAppM ``SemEnv.mk #[ns, ← mkAppM ``SemEnv.c #[env]]
      let tK ← mkAppM ``ConPastel.Translator.TEntry.K #[t]
      let tV ← mkAppM ``ConPastel.Translator.TEntry.V #[t]
      let nil := mkApp2 (mkConst ``Std.DHashMap.Internal.AssocList.nil [levelZero, levelZero]) tK
        (← withLocalDeclD `x tK fun x => mkLambdaFVars #[x] tV)
      mkForallFVars #[ns] (← mkAppM ``Eval #[env', e, mkApp (← mkAppM ``ConPastel.Translator.TEntry.BI #[t]) nil])
    mkLambdaFVars #[e, t] body
  let entTy := mkConst ``ConPastel.Translator.TEntry
  let mut hnil ← mkAppOptM ``List.Forall₂.nil #[mkConst ``Exp, entTy, R]
  let mut enilsL : List Expr := []
  let mut entsL : List Expr := []
  for ((cn, pn), e) in (nils.toList.zip ents).reverse do
    hnil ← mkAppOptM ``List.Forall₂.cons #[mkConst ``Exp, entTy, R, cn, e, ← mkListLit (mkConst ``Exp) enilsL,
      ← mkListLit entTy entsL, pn, hnil]
    enilsL := cn :: enilsL
    entsL := e :: entsL
  let enils ← mkListLit (mkConst ``Exp) enilsL
  -- the plain part
  let cpv ← mkFreshExprMVar (mkConst ``Exp)
  let plainInit := (← whnfR (mkApp2 plainE init (mkBVar 0))).eta
  let PI ← withLocalDeclD `v (mkConst ``Value) fun v => do
    let b ← whnfR (mkApp2 plainE init v)
    pure b.appFn!.appFn!
  let _ := plainInit
  -- the plain part of `init`, the projection of its literal reduced
  let pv ← whnf (mkApp (mkConst info.plainAcc) init)
  let gpv ← mkFreshExprMVar (← mkAppM ``Eval #[env, cpv, mkApp PI pv])
  solve gpv.mvarId!
  let hi ← mkAppOptM ``ConPastel.Translator.initRec_ok' #[σ, tabsE, plainE, env, mlString stname, mlString aname,
    ← instantiateMVars cpv, enils, init, hraw, hnil, ← instantiateMVars gpv]
  -- the run
  let envH (b loc : Expr) : GoalM Expr := do
    mkAppM ``SemEnv.mk #[← mkAppM ``nsOptBind #[← mkAppM ``Option.some #[mlString hname],
      ← mkAppM ``Value.loc #[b, loc], ← mkAppM ``SemEnv.v #[env]], ← mkAppM ``SemEnv.c #[env]]
  let rf ← withLocalDeclD `loc (mkConst ``Nat) fun loc => do
    mkLambdaFVars #[loc] (← mkAppOptM ``ConPastel.Translator.recRel #[σ, tabsE, plainE, loc])
  let invM ← mkAppOptM ``MRET #[σ, ε, α, rf, A, B]
  let cm ← mkFreshExprMVar (mkConst ``Exp)
  let hm ← withLocalDeclD `b (mkConst ``Bool) fun b => do
    withLocalDeclD `loc (mkConst ``Nat) fun loc => do
      let env' ← envH b loc
      let gm ← mkFreshExprMVar (← mkAppM ``Eval #[env', cm, mkApp invM m])
      solve gm.mvarId!
      mkLambdaFVars #[b, loc] (← instantiateMVars gm)
  let okF ← mkAppOptM ``Except.ok #[ε, α]
  let errF ← mkAppOptM ``Except.error #[ε, α]
  let cok ← mkFreshExprMVar (mkConst ``Exp)
  let hok ← withLocalDeclD `b (mkConst ``Bool) fun b => do
    withLocalDeclD `loc (mkConst ``Nat) fun loc => do
    withLocalDeclD `a α fun a => do
    withLocalDeclD `av (mkConst ``Value) fun av => do
    withLocalDeclD `hA (mkApp2 A a av) fun hA => do
      let env' ← envH b loc
      let env'' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsOptBind #[← mkAppM ``Option.some #[mlString xname], av,
        ← mkAppM ``SemEnv.v #[env']], ← mkAppM ``SemEnv.c #[env]]
      modify fun s => { s with locals := s.locals.push { fvar := a, cname := xname, value := av, rel := hA } }
      let gk ← mkFreshExprMVar (← mkAppM ``Eval #[env'', cok, mkApp inv (mkApp okF a)])
      solve gk.mvarId!
      modify fun s => { s with locals := s.locals.pop }
      mkLambdaFVars #[b, loc, a, av, hA] (← instantiateMVars gk)
  let cerr ← mkFreshExprMVar (mkConst ``Exp)
  let herr ← withLocalDeclD `b (mkConst ``Bool) fun b => do
    withLocalDeclD `loc (mkConst ``Nat) fun loc => do
    withLocalDeclD `e ε fun e => do
    withLocalDeclD `ev (mkConst ``Value) fun ev => do
    withLocalDeclD `hB (mkApp2 B e ev) fun hB => do
      let env' ← envH b loc
      let pty ← mkAppM ``Prod #[mkConst ``VarN, mkConst ``Value]
      let al ← mkListLit pty [← mkAppM ``Prod.mk #[mlString yname, ev]]
      let env'' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsAppend #[← mkAppOptM ``alistToNs #[mkConst ``ModN, none, none, al],
        ← mkAppM ``SemEnv.v #[env']], ← mkAppM ``SemEnv.c #[env]]
      modify fun s => { s with locals := s.locals.push { fvar := e, cname := yname, value := ev, rel := hB } }
      let gk ← mkFreshExprMVar (← mkAppM ``Eval #[env'', cerr, mkApp inv (mkApp errF e)])
      solve gk.mvarId!
      modify fun s => { s with locals := s.locals.pop }
      mkLambdaFVars #[b, loc, e, ev, hB] (← instantiateMVars gk)
  let ei ← mkAppM ``ConPastel.Translator.initRec #[mlString stname, mlString aname, ← instantiateMVars cpv, enils]
  let pf ← mkAppOptM ``ConPastel.Translator.Eval_runState #[σ, ε, α, none, rf, A, B, inv, env, ei,
    ← instantiateMVars cm, ← instantiateMVars cok, ← instantiateMVars cerr, mlString hname, mlString xname,
    mlString yname, init, m, okF, errF, hi, hm, hok, herr]
  let pty ← inferType pf
  let some (_, ceP, _) := (← whnfR pty).getAppFnArgs.2.toList.toArray[1]? |>.map (fun c => ((), c, ())) | throwError "runRef: proof"
  unless ← isDefEq ce ceP do throwError "runRef: code mismatch"
  assignProof g pf

/-- `runArr n x m` at a registered array state: `m` on a fresh CakeML array
`Array.array n x` (`Eval_runArr`). -/
partial def solveRunArr (g : MVarId) (env inv : Expr) (args : Array Expr) : GoalM Unit := do
  let #[el, ε, α, nE, x₀, m] := args | throwError "runArr: arguments"
  let S ← invOf el
  let σ ← mkAppM ``Array #[el]
  let A ← invOf α
  let B ← invOf ε
  let hname ← freshCName "h"
  let xname ← freshCName "x"
  let yname ← freshCName "y"
  let ce ← evalGoalCe g
  let cn ← mkFreshExprMVar (mkConst ``Exp)
  let gn ← mkFreshExprMVar (← mkAppM ``Eval #[env, cn, mkApp (mkConst ``NAT) nE])
  solve gn.mvarId!
  let ci ← mkFreshExprMVar (mkConst ``Exp)
  let gi ← mkFreshExprMVar (← mkAppM ``Eval #[env, ci, mkApp S x₀])
  solve gi.mvarId!
  let envH (b loc : Expr) : GoalM Expr := do
    mkAppM ``SemEnv.mk #[← mkAppM ``nsOptBind #[← mkAppM ``Option.some #[mlString hname],
      ← mkAppM ``Value.loc #[b, loc], ← mkAppM ``SemEnv.v #[env]], ← mkAppM ``SemEnv.c #[env]]
  let rf ← withLocalDeclD `loc (mkConst ``Nat) fun loc => do
    mkLambdaFVars #[loc] (← mkAppM ``ConPastel.Translator.arrRel #[S, loc])
  let invM ← mkAppOptM ``MRET #[σ, ε, α, rf, A, B]
  let cm ← mkFreshExprMVar (mkConst ``Exp)
  let hm ← withLocalDeclD `b (mkConst ``Bool) fun b => do
    withLocalDeclD `loc (mkConst ``Nat) fun loc => do
      let env' ← envH b loc
      let gm ← mkFreshExprMVar (← mkAppM ``Eval #[env', cm, mkApp invM m])
      solve gm.mvarId!
      mkLambdaFVars #[b, loc] (← instantiateMVars gm)
  let okF ← mkAppOptM ``Except.ok #[ε, α]
  let errF ← mkAppOptM ``Except.error #[ε, α]
  let cok ← mkFreshExprMVar (mkConst ``Exp)
  let hok ← withLocalDeclD `b (mkConst ``Bool) fun b => do
    withLocalDeclD `loc (mkConst ``Nat) fun loc => do
    withLocalDeclD `a α fun a => do
    withLocalDeclD `av (mkConst ``Value) fun av => do
    withLocalDeclD `hA (mkApp2 A a av) fun hA => do
      let env' ← envH b loc
      let env'' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsOptBind #[← mkAppM ``Option.some #[mlString xname], av,
        ← mkAppM ``SemEnv.v #[env']], ← mkAppM ``SemEnv.c #[env]]
      modify fun s => { s with locals := s.locals.push { fvar := a, cname := xname, value := av, rel := hA } }
      let gk ← mkFreshExprMVar (← mkAppM ``Eval #[env'', cok, mkApp inv (mkApp okF a)])
      solve gk.mvarId!
      modify fun s => { s with locals := s.locals.pop }
      mkLambdaFVars #[b, loc, a, av, hA] (← instantiateMVars gk)
  let cerr ← mkFreshExprMVar (mkConst ``Exp)
  let herr ← withLocalDeclD `b (mkConst ``Bool) fun b => do
    withLocalDeclD `loc (mkConst ``Nat) fun loc => do
    withLocalDeclD `e ε fun e => do
    withLocalDeclD `ev (mkConst ``Value) fun ev => do
    withLocalDeclD `hB (mkApp2 B e ev) fun hB => do
      let env' ← envH b loc
      let pty ← mkAppM ``Prod #[mkConst ``VarN, mkConst ``Value]
      let al ← mkListLit pty [← mkAppM ``Prod.mk #[mlString yname, ev]]
      let env'' ← mkAppM ``SemEnv.mk #[← mkAppM ``nsAppend #[← mkAppOptM ``alistToNs #[mkConst ``ModN, none, none, al],
        ← mkAppM ``SemEnv.v #[env']], ← mkAppM ``SemEnv.c #[env]]
      modify fun s => { s with locals := s.locals.push { fvar := e, cname := yname, value := ev, rel := hB } }
      let gk ← mkFreshExprMVar (← mkAppM ``Eval #[env'', cerr, mkApp inv (mkApp errF e)])
      solve gk.mvarId!
      modify fun s => { s with locals := s.locals.pop }
      mkLambdaFVars #[b, loc, e, ev, hB] (← instantiateMVars gk)
  let pf ← mkAppOptM ``Eval_runArr #[el, ε, α, none, S, A, B, inv, env, ← instantiateMVars cn, ← instantiateMVars ci,
    ← instantiateMVars cm, ← instantiateMVars cok, ← instantiateMVars cerr, mlString hname, mlString xname,
    mlString yname, nE, x₀, m, okF, errF, ← instantiateMVars gn, ← instantiateMVars gi, hm, hok, herr]
  let pty ← inferType pf
  let some (_, ceP, _) := (← whnfR pty).getAppFnArgs.2.toList.toArray[1]? |>.map (fun c => ((), c, ())) | throwError "runArr: proof"
  unless ← isDefEq ce ceP do throwError "runArr: code mismatch"
  assignProof g pf

/-- `a.toList` of a Braun-tree array (`treeArrayElem?`): the list of its tree,
`a.toList = (toA a).toList` (`toList_toA`). -/
partial def solveArrayToList (g : MVarId) (env inv a : Expr) : GoalM Unit := do
  let heq ← mkAppM ``ConPastel.Braun.toList_toA #[a]
  let some (_, lhs, rhs) := (← inferType heq).eq? | throwError "solveArrayToList: bad lemma"
  let ce ← evalGoalCe g
  let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv rhs])
  solve gb.mvarId!
  let motive ← withLocalDeclD `x (← inferType rhs) fun x => do
    mkLambdaFVars #[x] (← mkAppM ``Eval #[env, ce, mkApp inv x])
  let pf ← mkEqMP (← mkCongrArg motive (← mkEqSymm heq)) (← instantiateMVars gb)
  let g ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ce, mkApp inv lhs])
  g.assign pf

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
  if dep && inv.isAppOf ``NEWTYPE then return ← solveDepCasesNewtype g env inv fn np args τ
  -- a dependent motive (e.g. a result type indexed by the scrutinee): `Eval`'s
  -- predicate is on values only, so the clauses are translated at their own
  -- instances of the motive, each with the invariant of its own type
  let invAt (x : Expr) : MetaM Expr := do
    if dep then invOf (← instantiateMVars (motive.beta #[x])).headBeta else pure inv
  unless major.isFVar do
    if dep then throwError "dependent casesOn on a non-variable {major}"
    let letT := Expr.letE `z τ major (mkAppN fn (args[:np].toArray ++ #[motive, .bvar 0] ++ alts)) false
    let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv letT])
    return ← solve g'
  let st ← get
  let some lv := st.locals.find? (·.fvar == major) | throwError "unknown scrutinee {major}"
  let some hc := ctx.hasCons.find? d.name | throwError "no constructor environment for {τ}"
  let invT := mkConst (d.name ++ `cakeInv)
  let hl ← proveLookupG env lv.cname lv.value ctx.unfoldRec
  let he ← if lv.lazy then mkAppM ``Eval_force #[← evalLocal env lv hl]
    else mkAppOptM ``Eval_var #[env, shortIdent lv.cname, lv.value, mkApp invT major, hl, lv.rel]
  let qfun ← withLocalDeclD `x τ fun x => do
    mkLambdaFVars #[x] (mkApp (← invAt x) (mkAppN fn (args[:np].toArray ++ #[motive, x] ++ alts)))
  let mut lemArgs : Array (Option Expr) := #[some env, some hc, none, some major, some he, some qfun]
  let params := τ.getAppArgs
  let .const _ lvls := τ.getAppFn | unreachable!
  for k in [0:d.ctors.size] do
    let (c, _, dataFlags) := d.ctors[k]!
    let cty ← instantiateForall (← instantiateTypeLevelParams (← getConstInfo c).toConstantVal lvls) params
    let m := d.cached.size
    -- the stored items before the data fields: the cached fields, then the token
    let mt := m + (if d.token then 1 else 0)
    let cnames ← (List.range mt).mapM fun _ => freshCName "c"
    let names ← (dataFlags.toList.filter id).mapM fun _ => freshCName "f"
    let nameList ← mkListLit (mkConst ``VarN) ((cnames ++ names).map mlString)
    let hnd ← closeWith (← mkAppM ``List.Nodup #[nameList]) (← `(tactic| decide))
    let bk ← mkFreshExprMVar (mkConst ``Exp)
    let hk ← forallTelescope cty fun as _ => do
      let ctorApp := mkAppN (mkAppN (mkConst c lvls) params) as
      withLocalDeclD `heq (← mkEq major ctorApp) fun heq => do
      let dataAs := (as.toList.zip dataFlags.toList).filterMap fun (a, b) => if b then some a else none
      -- the cached fields' stored values come first
      withLocalDeclsDND ((Array.range mt).map fun i => (Name.mkSimple s!"z{i}", mkConst ``Value)) fun zs => do
      withLocalDeclsDND (dataAs.toArray.mapIdx fun i _ => (Name.mkSimple s!"w{i}", mkConst ``Value)) fun ws => do
      let dataJs := (List.range dataFlags.size).filter fun j => dataFlags[j]!
      let lazyF := dataJs.toArray.map fun j => d.lazy.contains (k, j)
      let invs ← (dataAs.toArray.zip lazyF).mapM fun (a, lz) => do
        let i ← invOf (← inferType a)
        if lz then mkAppM ``LAZY #[i] else pure i
      withLocalDeclsDND ((Array.range mt).map fun i => (Name.mkSimple s!"hz{i}",
          if i < m then mkApp2 (mkConst (d.name ++ Name.mkSimple s!"c{i}")) (mkApp (mkConst d.cached[i]!) ctorApp) zs[i]!
          else mkApp (mkConst ``TOKEN) zs[i]!)) fun hzs => do
      withLocalDeclsDND (dataAs.toArray.mapIdx fun i a => (Name.mkSimple s!"hw{i}", mkApp2 invs[i]! a ws[i]!)) fun hws => do
        let wList ← mkListLit (mkConst ``Value) (zs.toList ++ ws.toList)
        let envK ← mkAppM ``clauseEnv #[env, nameList, wList]
        let branchT := (mkAppN alts[k]! as).headBeta
        let gb ← mkFreshExprMVar (← mkAppM ``Eval #[envK, bk, mkApp (← invAt ctorApp) branchT])
        let saved := (← get).locals
        let savedA := (← get).aliases
        modify fun s => { s with aliases := s.aliases.push (ctorApp, lv, heq) }
        for i in [0:dataAs.length] do
          let lv : GLVar := { fvar := dataAs[i]!, cname := names[i]!, value := ws[i]!, rel := hws[i]!, lazy := lazyF[i]! }
          modify fun s => { s with locals := s.locals.push lv }
        solve gb.mvarId!
        modify fun s => { s with locals := saved, aliases := savedA }
        mkLambdaFVars (as ++ #[heq] ++ zs ++ ws ++ hzs ++ hws) (← instantiateMVars gb)
    lemArgs := lemArgs ++ (cnames ++ names).toArray.map (some ∘ mlString) ++ #[some hnd, some bk, some hk]
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
  let he ← if lv.lazy then mkAppM ``Eval_force #[← evalLocal env lv hl]
    else mkAppOptM ``Eval_var #[env, shortIdent lv.cname, lv.value, mkApp invL major, hl, lv.rel]
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
    -- without structure eta: `whnfCore` would otherwise go on into the branch and
    -- turn a `match` on a pair-valued call into one call per projection
    -- (exponential in a recursion such as `let (bs, e) := piBinders b; …`)
    let r ← withConfig (fun c => { c with etaStruct := .none }) do
      whnfCore (mkAppN (← instantiateValueLevelParams ci lvls) t'.getAppArgs).headBeta
    -- stuck on a structure's recursor (the scrutinee is not a constructor): back to
    -- `S.casesOn` (`motive, minor, major` becomes `motive, major, minor`)
    if let .const rn rlvls := r.getAppFn then
      if let some (.recInfo ri) := (← getEnv).find? rn then
        let rargs := r.getAppArgs
        if ri.numMotives == 1 && ri.numMinors == 1 && ri.numIndices == 0 &&
            rargs.size ≥ ri.numParams + 3 then
          let I := rn.getPrefix
          let np := ri.numParams
          return mkAppN (mkConst (I ++ `casesOn) rlvls)
            (rargs[:np].toArray ++ #[rargs[np]!, rargs[np + 2]!, rargs[np + 1]!] ++ rargs[np + 3:].toArray)
    pure r

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
      -- defined functions are not (whnf would unfold them), nor applications of
      -- local functions (a recursive call: structure eta would evaluate it once
      -- per projection, exponentially in the recursion)
      if d.isApp && d.getAppFn.isFVar then return false
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
  -- `match h : (b : Bool) with | true => A h | false => B h` (non-dependent):
  -- `if h : b = true then A h else B _` (the alternatives' `h` mention `b` itself,
  -- so the discriminant cannot be let-bound)
  if let some info ← getMatcherInfo? fnName then
    if info.numDiscrs == 1 && info.numAlts == 2 && info.altNumParams == #[1, 1] &&
        (info.discrInfos[0]!.hName?.isSome) then
      let d := args[info.numParams + 1]!
      let motive := args[info.numParams]!
      if (← whnfD (← inferType d)).isConstOf ``Bool && !d.isFVar &&
          (motive.isLambda && !motive.bindingBody!.hasLooseBVars) then
        let mci ← getConstInfo fnName
        let altCtors ← forallTelescope (← instantiateTypeLevelParams mci.toConstantVal lvls) fun xs _ => do
          (List.range 2).toArray.mapM fun j => do
            forallTelescope (← inferType xs[info.numParams + 2 + j]!) fun _ r => pure r.appArg!
        let jt? := altCtors.findIdx? (·.isConstOf ``Bool.true)
        let jf? := altCtors.findIdx? (·.isConstOf ``Bool.false)
        if let (some jt, some jf) := (jt?, jf?) then
          let altT := args[info.numParams + 2 + jt]!
          let altF := args[info.numParams + 2 + jf]!
          let cond ← mkEq d (mkConst ``Bool.true)
          let thenF ← withLocalDeclD `h cond fun h => do mkLambdaFVars #[h] (altT.beta #[h])
          let elseF ← withLocalDeclD `h (mkNot cond) fun h => do
            mkLambdaFVars #[h] (altF.beta #[← mkAppM ``Iff.mpr #[← mkAppOptM ``Bool.eq_false_iff #[d], h]])
          let t' ← mkAppM ``dite #[cond, thenF, elseF]
          let heq ← closeWith (← mkEq t t') (← `(tactic|
            (split <;> rename_i hh <;> first | rw [dif_pos hh] | rw [dif_neg (by simp [hh])])))
          let ce ← evalGoalCe g
          let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv t'])
          solve gb.mvarId!
          let mot ← withLocalDeclD `x (← inferType t) fun x => do
            mkLambdaFVars #[x] (← mkAppM ``Eval #[env, ce, mkApp inv x])
          g.assign (← mkEqMP (← mkCongrArg mot (← mkEqSymm heq)) (← instantiateMVars gb))
          return
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
            if let some (.ctorInfo mci) := (← getEnv).find? mc then
              -- one iota step (a full `whnfR` would go on unfolding reducible
              -- auxiliaries in the selected branch, e.g. sparse `casesOn`s)
              let base := ii.numParams + 1 + ii.numIndices + 1
              if args.size ≥ base + ii.ctors.length && major.getAppNumArgs == mci.numParams + mci.numFields then
                let fields := major.getAppArgs[mci.numParams:].toArray
                let t' := (mkAppN (mkAppN args[base + mci.cidx]! fields) args[base + ii.ctors.length:].toArray).headBeta
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
  -- Braun-tree arrays (`treeArrayElem?`): the constructor, the list projection,
  -- the representation function `toA` and the canonical injection `ofAC`
  if let .const cn us := fn then
    if cn == ``Array.mk && args.size == 2 then
     if (← treeArrayElem? (← inferType t)).isSome then
      let (``NEWTYPE, #[_, _, _, A]) := inv.getAppFnArgs | throwError "array invariant {inv}"
      let t' ← mkAppM ``ConPastel.Braun.A.ofList #[args[1]!]
      let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp A t'])
      return ← solve g'
    if cn == ``Array.toList && args.size == 2 then
      -- (nested: a `←` inside `&&` would run before the size test)
      if (← treeArrayElem? (← inferType args[1]!)).isSome then
        return ← solveArrayToList g env inv args[1]!
    if cn == ``ConPastel.Braun.toA && args.size == 2 then
      let invS ← invOf (← inferType args[1]!)
      if invS.isAppOf ``NEWTYPE then
        let g' ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp invS args[1]!])
        return ← solve g'
    if cn == ``ConPastel.Braun.ofAC && args.size == 3 then
     if (← treeArrayElem? (← inferType t)).isSome then
      let (``NEWTYPE, #[_, _, _, A]) := inv.getAppFnArgs | throwError "array invariant {inv}"
      let ce ← evalGoalCe g
      let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp A args[1]!])
      solve gb.mvarId!
      let heq := mkAppN (mkConst ``ConPastel.Braun.toA_ofAC []) args
      let motive ← withLocalDeclD `w (← inferType args[1]!) fun w => do
        mkLambdaFVars #[w] (← mkAppM ``Eval #[env, ce, mkApp A w])
      let pf ← mkEqMP (← mkCongrArg motive (← mkEqSymm heq)) (← instantiateMVars gb)
      let g ← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ce, mkApp A (← inferType heq).appFn!.appArg!])
      g.assign pf
      return
  -- running a computation on a fresh reference
  if let .const cn _ := fn then
    if cn == ``ConPastel.Translator.runArr && args.size == 6 then
      if (← stateArrMonad? (← inferType args[5]!)).isSome then
        return ← solveRunArr g env inv args
    if cn == ``ConPastel.Translator.runRef && args.size == 5 then
      if let some (_, _, _, info) ← stateRecMonad? (← inferType args[4]!) then
        return ← solveRunRec g env inv args info
      if (← stateRefMonad? (← inferType args[4]!)).isSome then
        return ← solveRunRef g env inv args
  -- the pointer test `ptrSel a b t e h`: CakeML's `=` on `a` and `b` (sound at a
  -- type registered with `cake_eqsound_reg`), then `t` or `e`
  if fn.isConstOf ``ptrSel && args.size == 7 then
    let a := args[2]!; let b := args[3]!; let tf := args[4]!; let ev := args[5]!
    let invA ← invOf args[0]!
    let envS := eqSoundExt.getState (← getEnv)
    let some thm := (match invA.getAppFn with | .const n _ => envS.find? n | _ => none)
      | throwError "ptrSel: no EqSound theorem for {invA} (cake_eqsound_reg)"
    let (_, ga) ← newEvalGoal env (mkApp invA a)
    solve ga
    let (_, gb) ← newEvalGoal env (mkApp invA b)
    solve gb
    let ht ← withLocalDeclD `p (← mkEq a b) fun p => do
      let (_, gt) ← newEvalGoal env (mkApp inv (mkApp tf p).headBeta)
      solve gt
      mkLambdaFVars #[p] (← instantiateMVars (mkMVar gt))
    let (_, ge) ← newEvalGoal env (mkApp inv ev)
    solve ge
    let pf ← mkAppOptM ``Eval_ptrSel #[none, none, none, none, some (mkConst thm), none, none, none, none, none,
      some a, some b, some tf, some ev, some args[6]!, some (← instantiateMVars (mkMVar ga)), some (← instantiateMVars (mkMVar gb)),
      some ht, some (← instantiateMVars (mkMVar ge))]
    assignProof g pf
    return
  -- registered replacements `K xs = K' xs`
  if let .const c us := fn then
    if let some (rc, thm) := (replaceExt.getState (← getEnv)).find? c then
      -- an `Array` replacement (on the Braun tree) only where the array is a tree
      let mut skip := false
      if (`ConPastel.Braun).isPrefixOf rc && args.size > 0 then
        skip := (← whnfR args[0]!).isConstOf ``UInt8
      -- a monomorphic theorem (`cake_replace` at universe 0) applies at universe 0 only
      let thmMono := ((← getConstInfo thm).levelParams).isEmpty && !us.isEmpty
      skip := skip || (thmMono && !us.all (· == levelZero))
      let tus := if thmMono then [] else us
      let rcLevels := (← getConstInfo rc).levelParams
      let rus := if thmMono then rcLevels.map fun _ => levelZero else us
      if !skip then
        let n ← forallTelescope (← inferType (mkConst thm tus)) fun xs _ => pure xs.size
        -- a theorem between partial applications (`K xs = K' xs`) also rewrites
        -- longer applications `K xs ys`
        if args.size ≥ n then
          let heq := mkAppN (mkConst thm tus) (args.extract 0 n)
          let rest := args.extract n args.size
          let t' := mkAppN (mkAppN (mkConst rc rus) (args.extract 0 n)) rest
          let ce ← evalGoalCe g
          let gb ← mkFreshExprMVar (← mkAppM ``Eval #[env, ce, mkApp inv t'])
          solve gb.mvarId!
          let motive ← withLocalDeclD `x (← inferType (mkAppN fn (args.extract 0 n))) fun x => do
            mkLambdaFVars #[x] (← mkAppM ``Eval #[env, ce, mkApp inv (mkAppN x rest)])
          g.assign (← mkEqMP (← mkCongrArg motive (← mkEqSymm heq)) (← instantiateMVars gb))
          return
  -- matchers and sparse casesOn auxiliaries
  if let .const fnName _ := fn then
    if (← Meta.isMatcher fnName) then
      return ← solveMatcher g env inv t
    if let .str _ last := fnName then
      if last.startsWith "_sparseCasesOn" then
        return ← solveSparseCases g env inv t
  -- integers: `Int.ofNat n` is `n`'s value; `Int.add/sub/mul` are CakeML's integer arithmetic
  -- (`←` inside `&&` is hoisted before the guards: check the size first)
  if fn.isConstOf ``Nat.cast && args.size == 3 then
   if (← whnfR args[0]!).isConstOf ``Int then
    return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp (mkConst ``NAT) args[2]!]))
  if fn.isConstOf ``Int.ofNat && args.size == 1 then
    return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp (mkConst ``NAT) args[0]!]))
  if (fn.isConstOf ``Int.add || fn.isConstOf ``Int.sub || fn.isConstOf ``Int.mul) && args.size == 2 then
    let lem := if fn.isConstOf ``Int.add then ``Eval_int_add else if fn.isConstOf ``Int.sub then ``Eval_int_sub
      else ``Eval_int_mul
    let (_, ga) ← newEvalGoal env (mkApp (mkConst ``INT) args[0]!)
    let (_, gb) ← newEvalGoal env (mkApp (mkConst ``INT) args[1]!)
    solve ga; solve gb
    assignProof g (← mkAppM lem #[← instantiateMVars (mkMVar ga), ← instantiateMVars (mkMVar gb)])
    return
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
            -- a scrutinee that is not a variable is bound first: projecting it
            -- directly would evaluate it once per projection (exponential in a
            -- recursion such as `let (bs, e) := f b; …`)
            let mtyO ← inferType major
            let t' ← if major.isFVar then do
                let projs := (List.range ci.numFields).map fun i => Expr.proj tn i major
                pure (mkAppN (mkAppN args[ii.numParams + 2]! projs.toArray)
                  args[ii.numParams + 3:].toArray).headBeta
              else withLocalDeclD `z mtyO fun z => do
                let projs := (List.range ci.numFields).map fun i => Expr.proj tn i z
                let b := (mkAppN (mkAppN args[ii.numParams + 2]! projs.toArray)
                  args[ii.numParams + 3:].toArray).headBeta
                pure (Expr.letE `z mtyO major (b.abstract #[z]) false)
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
          -- cached fields: bind the data fields first (each is evaluated once, and the
          -- cached values read the children's stored fields)
          if !d.cached.isEmpty then
            let pending := (List.range fields.size).filter fun j => dataFlags[j]! && !fields[j]!.isFVar
            if !pending.isEmpty then
              let rec bindAll (js : List Nat) (fs : Array Expr) (acc : Array Expr) : MetaM Expr := do
                match js with
                | [] => mkLetFVars acc (mkAppN fn (args[:ci.numParams].toArray ++ fs))
                | j :: rest =>
                  withLetDecl `cf (← inferType fs[j]!) fs[j]! fun x => bindAll rest (fs.set! j x) (acc.push x)
              let t' ← bindAll pending fields #[]
              return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t']))
          let mut cpfs : Array Expr := #[]
          for c in [0:d.cached.size] do
            let some rhs ← unfoldDefinition? (mkApp (mkConst d.cached[c]!) t)
              | throwError "cannot unfold cached field {d.cached[c]!}"
            let rhs ← whnfCore rhs
            let (_, gc) ← newEvalGoal env (mkApp (mkConst (d.name ++ Name.mkSimple s!"c{c}")) rhs)
            solve gc
            cpfs := cpfs.push (← instantiateMVars (mkMVar gc))
          -- the identity token: a fresh reference
          if d.token then
            cpfs := cpfs.push (← mkAppM ``Eval_tok #[env])
          let mut pfs : Array Expr := #[]
          -- recursive fields are recognised as at registration: up to `normType`
          let τn ← normType τ
          for j in [0:fields.size] do
            if dataFlags[j]! then
              let fty ← normType (← inferType fields[j]!)
              let fi := if fty == τn then mkConst (d.name ++ `cakeInv)
                else mkConst (d.name ++ Name.mkSimple s!"f{k}_{j}")
              let (_, gj) ← newEvalGoal env (mkApp fi fields[j]!)
              solve gj
              pfs := pfs.push (← instantiateMVars (mkMVar gj))
          let nd := cpfs.size + pfs.size
          let lemArgs : Array (Option Expr) := #[some env, some hc] ++ Array.replicate nd none ++
            fields.map some ++ cpfs.map some ++ pfs.map some
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
  -- `I.rec` whose minor premises ignore their induction hypotheses is
  -- `I.casesOn` (compiled matches), possibly applied to further arguments
  if let .const recN lvls := fn then
    if recN != ``Nat.rec then
    if let some t' ← recAsCasesOn? recN lvls args then
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
      modify fun st => { st with decHint := some args[5]! }
      return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t']))
  -- calls to members of the mutual block: the joint induction hypothesis at `inj_j y`
  if let some mr := ctx.mrec? then
    if let .const cn _ := fn then
      if let some m := mr.members.find? (·.head == cn) then
        -- over-applied (e.g. a monadic state argument): peel the extra arguments
        if args.size > m.arity then
          return ← solvePeel g env (mkAppN fn args.pop) args.back!
        -- under-applied (a member as a function value): eta-expand
        if args.size < m.arity then
          let t' ← forallTelescope (← inferType t) fun xs _ => do
            let xs := xs[:m.arity - args.size].toArray
            mkLambdaFVars xs (mkAppN t xs)
          return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t']))
        if args.size == m.arity then
          let y ← if m.arity == 1 then pure args[0]! else
            args.pop.foldrM (fun a acc => mkAppM ``Prod.mk #[a, acc]) args.back!
          let q := (m.inj.beta #[y]).headBeta
          let relTy := mkApp2 mr.r q mr.s
          let hdec ← try closeDec relTy (← `(tactic| (subst_vars; (try simp only [WellFoundedRelation.rel, measure, InvImage, invImage, Nat.lt_wfRel] at *); (try dsimp only at *); first | omega | decreasing_tactic | (simp_wf; omega))))
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
  -- recursive calls (peel extra arguments, eta-expand partial applications)
  if let some r := ctx.rec? then
    if fn.isConstOf r.head && args.size > r.static.size + r.arity &&
        (args[:r.static.size].toArray == r.static) then
      return ← solvePeel g env (mkAppN fn args.pop) args.back!
    if fn.isConstOf r.head && args.size ≥ r.static.size && args.size < r.static.size + r.arity &&
        (args[:r.static.size].toArray == r.static) then
      let t' ← forallTelescope (← inferType t) fun xs _ => do
        let xs := xs[:r.static.size + r.arity - args.size].toArray
        mkLambdaFVars xs (mkAppN t xs)
      return ← solve (← g.replaceTargetDefEq (← mkAppM ``Eval #[env, ← evalGoalCe g, mkApp inv t']))
  if let some r := ctx.rec? then
    if fn.isConstOf r.head && args.size == r.static.size + r.arity &&
        (args[:r.static.size].toArray == r.static) then
      let ys := args[r.static.size:].toArray
      let y ← if r.arity == 1 then pure ys[0]! else
        ys.pop.foldrM (fun a acc => mkAppM ``Prod.mk #[a, acc]) ys.back!
      -- the IH at y: ∀ yv, A y yv → AppReturns cl yv (B (f y))
      let ihTy ← whnfR (← inferType r.ih)
      let .forallE _ _ body _ := ihTy | throwError "bad IH"
      let .forallE _ relTy0 _ _ := body.instantiate1 y | throwError "bad IH"
      -- a fibred relation (`wf_fiber`): the fixed parts agree definitionally
      let relW ← whnfR relTy0
      let (relTy, fixEq?) ← do
        if relW.isAppOfArity ``And 2 then
          if let some (_, l, r) := relW.appFn!.appArg!.eq? then
            if ← isDefEq l r then pure (relW.appArg!, some (← mkEqRefl l)) else pure (relTy0, none)
          else pure (relTy0, none)
        else pure (relTy0, none)
      let hint := (← get).decHint
      modify fun st => { st with decHint := none }
      let hinted ← match hint with
        | none => pure none
        | some h => do
          let hty ← inferType h
          if ← isDefEq hty relTy then pure (some h) else
          try
            let imp ← closeDec (← mkArrow hty relTy) (← `(tactic| (intro hh; subst_vars; exact hh)))
            pure (some (mkApp imp h))
          catch _ => pure none
      let hdec ← if let some h := hinted then pure h else
        try closeDec relTy (← `(tactic| first
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
      let hdec ← match fixEq? with
        | some e => mkAppM ``And.intro #[e, hdec]
        | none => pure hdec
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
            let some gv := ctx.globals.get? key |
              collectOrThrowNeed ctx.collectNeeds g key t
              return
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
            let some gv := ctx.globals.get? key |
              collectOrThrowNeed ctx.collectNeeds g key t
              return
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
        let some gv := ctx.globals.get? key |
          collectOrThrowNeed ctx.collectNeeds g key t
          return
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
