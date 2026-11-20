import ConPastel.Translator.Swap
import ConLeche.Cached.CoreC

/-!
# con-leche's state operations, as operations on a state record

con-leche's kernel state `CState` is translated as a record of hash tables
updated in place (`cake_state_record`, `ConPastel.Leche.KernelTypes`). Such a
state has no whole-state `get`/`set`: its operations are `hmFind`,
`hmInsertD`, `hmSize`, `hmClear` and `stRead` on single fields, and `swapRun`
for the eager memos. Each con-leche function that reads or writes the state
is equal to one written with those operations; the equations here are
registered with `cake_rewrite`, so that the translation sees the latter.
-/

set_option linter.all false

namespace ConPastel.Leche.StateRw
open ConLeche ConLeche.Cached ConPastel.Translator

/-! ## The memo wrappers -/

theorem memoEI_eq (get' : CState → Std.HashMap Expr Expr) (set' : CState → Std.HashMap Expr Expr → CState)
    (f : Nat → Expr → CheckCM Expr) (d : Nat) (e : Expr) :
    memoEI get' set' f d e = (do
      match ← hmFind get' e with
      | some r => pure r
      | none => do
        let r ← f d e
        hmInsertD get' set' e r
        pure r) := by
  funext st
  simp only [memoEI, hmFind, hmInsertD, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, Except.pure]
  cases (get' st)[e]? <;> simp only
  cases f d e st <;> rfl

theorem memoBI_eq (f : Nat → Expr → Expr → CheckCM Bool) (d : Nat) (a b : Expr) :
    memoBI f d a b = (do
      match ← hmFind (·.defeqC) (a, b) with
      | some r => pure r
      | none => do
        let r ← f d a b
        hmInsertD (·.defeqC) (fun st mp => { st with defeqC := mp }) (a, b) r
        pure r) := by
  funext st
  simp only [memoBI, hmFind, hmInsertD, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, Except.pure]
  cases st.defeqC[(a, b)]? <;> simp only
  cases f d a b st <;> rfl

theorem whnfCoreLookupI_eq (cheap : Bool) (e : Expr) :
    whnfCoreLookupI cheap e =
      (if cheap then hmFind (·.whnfCoreCheapC) e else hmFind (·.whnfCoreC) e) := by
  funext st
  cases cheap <;> rfl

/-- Store a chain's keys in the full mode's `whnfCore` memo. -/
def storeAllW (v : Expr) : List Expr → CheckCM Unit
  | [] => pure ()
  | k :: ks => do
    hmInsertD (·.whnfCoreC) (fun st mp => { st with whnfCoreC := mp }) k v
    storeAllW v ks

/-- Store a chain's keys in the cheap mode's `whnfCore` memo. -/
def storeAllWC (v : Expr) : List Expr → CheckCM Unit
  | [] => pure ()
  | k :: ks => do
    hmInsertD (·.whnfCoreCheapC) (fun st mp => { st with whnfCoreCheapC := mp }) k v
    storeAllWC v ks

theorem storeAllW_run (v : Expr) : ∀ (ks : List Expr) (st : CState),
    storeAllW v ks st = .ok ((), { st with whnfCoreC := ks.foldl (fun m k => m.insert k v) st.whnfCoreC })
  | [], st => rfl
  | k :: ks, st => by
    simp only [storeAllW, bind, StateT.bind, hmInsertD, Except.bind]
    rw [storeAllW_run v ks]
    rfl

theorem storeAllWC_run (v : Expr) : ∀ (ks : List Expr) (st : CState),
    storeAllWC v ks st = .ok ((), { st with whnfCoreCheapC := ks.foldl (fun m k => m.insert k v) st.whnfCoreCheapC })
  | [], st => rfl
  | k :: ks, st => by
    simp only [storeAllWC, bind, StateT.bind, hmInsertD, Except.bind]
    rw [storeAllWC_run v ks]
    rfl

theorem storeChainI_eq (cheap : Bool) (pend pendC : List Expr) (v : Expr) :
    storeChainI cheap pend pendC v =
      (if cheap || pend.isEmpty then pure () else do storeAllW v pend; storeAllWC v pendC) := by
  funext st
  unfold storeChainI
  split
  · rfl
  · simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind, Except.bind]
    rw [storeAllW_run]
    simp only
    rw [storeAllWC_run]
    rfl

/-! ## Bulk instantiation and level equivalence -/

theorem instListM_eq (e : Expr) (vs : List Expr) (d : Nat) :
    instListM e vs d = (if e.bvarB ≤ d then pure e else do
      match ← hmFind (·.instC) (e, vs, d) with
      | some r => pure r
      | none => do
        let sz ← hmSize (·.instC)
        if sz < instCCapC then pure () else hmClear (·.instC) (fun st mp => { st with instC := mp })
        let r := Expr.instantiateListC e vs d
        hmInsertD (·.instC) (fun st mp => { st with instC := mp }) (e, vs, d) r
        pure r) := by
  funext st
  simp only [instListM, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  split
  · rfl
  · simp only [hmFind, hmSize, hmClear, hmInsertD, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure]
    cases st.instC[(e, vs, d)]? with
    | some r => rfl
    | none =>
      simp only
      by_cases hc : st.instC.size < instCCapC
      · simp only [hc, if_true, hmSize, hmInsertD, hmClear, bind, StateT.bind, Except.bind, StateT.pure, Except.pure,
          decide_true]
        rfl
      · simp only [hc, if_false, hmSize, hmInsertD, hmClear, bind, StateT.bind, Except.bind, StateT.pure, Except.pure,
          decide_false]
        rfl

/-- The level-simplification memo. -/
def simpLM (l : Level) : CheckCM Level := do
  match ← hmFind (·.lsimpC) l with
  | some x => pure x
  | none => do
    let x := Level.simplify l
    hmInsertD (·.lsimpC) (fun st mp => { st with lsimpC := mp }) l x
    pure x

theorem isEquivLM_eq (l r : Level) :
    isEquivLM l r = (if l == r then pure (some true) else do
      match ← hmFind (·.eqvC) (l, r) with
      | some b => pure (some b)
      | none => do
        let ls ← simpLM l
        let rs ← simpLM r
        if ls == rs then do
          hmInsertD (·.eqvC) (fun st mp => { st with eqvC := mp }) (l, r) true
          pure (some true)
        else
          match Level.leqCore Level.defaultFuel ls rs 0 with
          | some false => do
            hmInsertD (·.eqvC) (fun st mp => { st with eqvC := mp }) (l, r) false
            pure (some false)
          | some true =>
            match Level.leqCore Level.defaultFuel rs ls 0 with
            | some b => do
              hmInsertD (·.eqvC) (fun st mp => { st with eqvC := mp }) (l, r) b
              pure (some b)
            | none => pure none
          | none => pure none) := by
  funext st
  simp only [isEquivLM]
  split
  · rfl
  · simp only [modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, hmFind, hmInsertD, simpLM, bind,
      StateT.bind, Except.bind, pure, StateT.pure]
    cases hq : st.eqvC[(l, r)]? with
    | some b => rfl
    | none =>
      simp only [simpLM, hmFind, hmInsertD, StateT.bind, Except.bind, StateT.pure, Except.pure]
      cases h1 : st.lsimpC[l]? with
      | some x =>
        simp only
        cases h2 : st.lsimpC[r]? with
        | some y =>
          simp only [bind, Except.bind, StateT.bind, StateT.pure, Except.pure, pure, hmFind, hmInsertD, h1, h2]
          repeat' split
          all_goals simp_all only [bind, Except.bind, StateT.bind, StateT.pure, Except.pure, pure, hmInsertD,
            Bool.false_eq_true, ite_true, ite_false, reduceCtorEq, Option.some.injEq]
        | none =>
          simp only [bind, Except.bind, StateT.bind, StateT.pure, Except.pure, pure, hmFind, hmInsertD, h1, h2]
          repeat' split
          all_goals simp_all only [bind, Except.bind, StateT.bind, StateT.pure, Except.pure, pure, hmInsertD,
            Bool.false_eq_true, ite_true, ite_false, reduceCtorEq, Option.some.injEq]
      | none =>
        simp only
        cases h2 : (st.lsimpC.insert l l.simplify)[r]? with
        | some y =>
          simp only [bind, Except.bind, StateT.bind, StateT.pure, Except.pure, pure, hmFind, hmInsertD, h1, h2]
          repeat' split
          all_goals simp_all only [bind, Except.bind, StateT.bind, StateT.pure, Except.pure, pure, hmInsertD,
            Bool.false_eq_true, ite_true, ite_false, reduceCtorEq, Option.some.injEq]
        | none =>
          simp only [bind, Except.bind, StateT.bind, StateT.pure, Except.pure, pure, hmFind, hmInsertD, h1, h2]
          repeat' split
          all_goals simp_all only [bind, Except.bind, StateT.bind, StateT.pure, Except.pure, pure, hmInsertD,
            Bool.false_eq_true, ite_true, ite_false, reduceCtorEq, Option.some.injEq]

/-! ## The stored-constant caches -/

theorem constTyAtM_eq (fe : FEnv) (nI n : Name) (us : List Level) :
    constTyAtM fe nI n us = (do
      let hit? ← hmFind (·.constTyAt) (n, us)
      match hit? with
      | some i => pure i
      | none =>
        match fe.find? n with
        | some ci =>
          let cv := ci.toConstantVal
          let i ← instLevelParamsM cv.levelParams us cv.type
          hmInsertD (·.constTyAt) (fun st mp => { st with constTyAt := mp }) (n, us) i
          pure i
        | none => throw (.internal "constTyAtM: unknown constant")) := rfl

theorem constValAtM_eq (fe : FEnv) (nI n : Name) (us : List Level) :
    constValAtM fe nI n us = (do
      let hit? ← hmFind (·.constValAt) (n, us)
      match hit? with
      | some i => pure i
      | none =>
        match fe.find? n with
        | some (.defnInfo cv v _) =>
          let i ← instLevelParamsM cv.levelParams us v
          hmInsertD (·.constValAt) (fun st mp => { st with constValAt := mp }) (n, us) i
          pure i
        | _ => throw (.internal "constValAtM: not a stored definition")) := rfl

theorem ruleRhsAtM_eq (fe : FEnv) (cI jI c j : Name) (us : List Level) :
    ruleRhsAtM fe cI jI c j us = (do
      let hit? ← hmFind (·.ruleRhsAt) (c, j, us)
      match hit? with
      | some i => pure i
      | none =>
        match fe.find? c with
        | some (.recInfo cv _ _ _ rules) =>
          match rules.find? (fun r' => r'.ctor == j) with
          | some rl =>
            let i ← instLevelParamsM cv.levelParams us rl.rhs
            hmInsertD (·.ruleRhsAt) (fun st mp => { st with ruleRhsAt := mp }) (c, j, us) i
            pure i
          | none => throw (.internal "ruleRhsAtM: no rule for constructor")
        | _ => throw (.internal "ruleRhsAtM: not a stored recursor")) := rfl

/-! ## The plain part, flushing, and the eager memos -/

theorem maxNatSizeM_eq : maxNatSizeM = stRead (·.maxNatSize) := rfl

theorem flushC_eq : flushC = (do
    hmClear (·.constTyAt) (fun st mp => { st with constTyAt := mp })
    hmClear (·.constValAt) (fun st mp => { st with constValAt := mp })
    hmClear (·.ruleRhsAt) (fun st mp => { st with ruleRhsAt := mp })
    hmClear (·.whnfCoreC) (fun st mp => { st with whnfCoreC := mp })
    hmClear (·.whnfCoreCheapC) (fun st mp => { st with whnfCoreCheapC := mp })
    hmClear (·.whnfC) (fun st mp => { st with whnfC := mp })
    hmClear (·.inferC) (fun st mp => { st with inferC := mp })
    hmClear (·.inferIOC) (fun st mp => { st with inferIOC := mp })
    hmClear (·.defeqC) (fun st mp => { st with defeqC := mp })
    hmClear (·.instC) (fun st mp => { st with instC := mp })
    hmClear (·.eagerMemos.whnfCoreC) (fun st mp => { st with eagerMemos := { st.eagerMemos with whnfCoreC := mp } })
    hmClear (·.eagerMemos.whnfCoreCheapC)
      (fun st mp => { st with eagerMemos := { st.eagerMemos with whnfCoreCheapC := mp } })
    hmClear (·.eagerMemos.whnfC) (fun st mp => { st with eagerMemos := { st.eagerMemos with whnfC := mp } })
    hmClear (·.eagerMemos.inferC) (fun st mp => { st with eagerMemos := { st.eagerMemos with inferC := mp } })
    hmClear (·.eagerMemos.inferIOC) (fun st mp => { st with eagerMemos := { st.eagerMemos with inferIOC := mp } })
    hmClear (·.eagerMemos.defeqC) (fun st mp => { st with eagerMemos := { st.eagerMemos with defeqC := mp } }) :
    CheckCM Unit) := rfl

/-- Entering the eager tower from a plain mode. -/
def enterE (st : CState) : CState := (CState.enterEager false st).2
/-- Leaving it: the plain memos of the state the eager run started from return. -/
def leaveE (st₂ st : CState) : CState := st₂.leaveEager (some st.modeMemos)

theorem withEagerMemos_eq {α : Type} (eager : Bool) (x : CheckCM α) :
    withEagerMemos eager x = (if eager then x else swapRun enterE leaveE x) := by
  funext st
  cases eager with
  | true =>
    simp only [withEagerMemos, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, modify, bind, StateT.bind,
      Except.bind, pure, StateT.pure, Except.pure, CState.enterEager, CState.leaveEager, ite_true]
    cases x st <;> rfl
  | false =>
    simp only [withEagerMemos, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, modify, bind, StateT.bind,
      Except.bind, pure, StateT.pure, Except.pure, swapRun, enterE, leaveE, Bool.false_eq_true, ite_false]
    cases x (CState.enterEager false st).2 <;> rfl

end ConPastel.Leche.StateRw
