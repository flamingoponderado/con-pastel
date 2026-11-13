import ConPastel.Main.ReadAll
import ConPastel.Program.ConCheck
import ConPastel.Translator.Tuple

/-!
# The main program is correct

`mainRun`: in an environment where `entry` and `revApp` are bound to values
satisfying their certificates, the main declarations run from a state whose
FFI is `initFfi input` (plus earlier events that are not writes), and write
exactly `verdictBytes (entry (byteNats input))`.
-/

namespace ConPastel.Main
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString ConPastel.Translator ConPastel.Program

theorem evaluate_nil_list {σ : Type} (s : State σ) (env : SemEnv Value) :
    evaluate s env [] = (s, .val []) := by
  rw [evaluate]

theorem revApp_eq (xs acc : List Nat) : revApp xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp [revApp]
  | cons x xs ih => simp [revApp, ih]

/-! ## Runs of basic expressions in any state -/

theorem Runs.var {σ : Type} (s : State σ) (env : SemEnv Value) (n : String) (v : Value)
    (h : nsLookup env.v (.short (ofString n)) = some v) : Runs s env [var n] s (.val [v]) :=
  ⟨0, 0, by simp [ConPastel.Main.var, evaluate, h]⟩

theorem Runs.of_evalRel {σ : Type} {s s' : State σ} {env : SemEnv Value} {e : Exp} {v : Value}
    (h : EvalRel s env e s' v) : Runs s env [e] s' (.val [v]) := h

/-- A pure expression with an `Eval` certificate runs in any state, appending to the store. -/
theorem Runs.of_eval {σ : Type} (s : State σ) {env : SemEnv Value} {e : Exp} {P : Value → Prop}
    (h : Eval env e P) : ∃ v refs, Runs s env [e] { s with refs := s.refs ++ refs } (.val [v]) ∧ P v := by
  obtain ⟨v, refs, hr, hp⟩ := h σ s
  exact ⟨v, refs, hr, hp⟩

/-- Applying a function value with an `AppReturns` fact, once the arguments have run. -/
theorem Runs.app_returns {σ : Type} {s s₁ : State σ} {env : SemEnv Value} {ef ex : Exp}
    {vf vx : Value} {P : Value → Prop} (hargs : Runs s env [ex, ef] s₁ (.val [vx, vf]))
    (happ : AppReturns vf vx P) :
    ∃ v refs, Runs s env [.app .opapp [ef, ex]] { s₁ with refs := s₁.refs ++ refs } (.val [v]) ∧ P v := by
  obtain ⟨env', body, hdo, v, refs, hrel, hp⟩ := happ σ s₁
  exact ⟨v, refs, Runs.app_opapp hargs hdo hrel, hp⟩

/-! ## The main declarations, step by step -/

/-- `Word8Array.array 2 0w`. -/
theorem eval_alloc {σ : Type} (s : State σ) (env : SemEnv Value) :
    evaluate s env [.app .aw8alloc [.lit (.intLit 2), .lit (.word8 0)]] =
      ({ s with refs := s.refs ++ [.w8array [0, 0]] }, .val [.loc true s.refs.length]) := by
  simp [evaluate, fixClock, getOpClass, headValue, Flapjack.holHd, doApp, doAppNumericCore,
    doAppBasic, storeAlloc, listResult]

/-- `con none args`, once the arguments have run (right to left). -/
theorem Runs.con_none {σ : Type} {s s' : State σ} {env : SemEnv Value} {args : List Exp}
    {vs : List Value} (h : Runs s env args.reverse s' (.val vs)) :
    Runs s env [.con none args] s' (.val [.conv none vs.reverse]) := by
  obtain ⟨a₁, a₂, ha⟩ := h
  refine ⟨a₁, a₂, ?_⟩
  rw [evaluate]
  simp [doConCheck, ha, buildConv]

/-- A nullary constructor in scope. -/
theorem Runs.con_nil {σ : Type} (s : State σ) {env : SemEnv Value} (hc : HasListCons env.c) :
    Runs s env [.con (some (.short (ofString "[]"))) []] s
      (.val [.conv (some (.typeStamp nilC 1)) []]) := by
  refine ⟨0, 0, ?_⟩
  have hl : nsLookup env.c (.short (ofString "[]")) = some (0, .typeStamp nilC 1) := hc.nil
  rw [evaluate]
  simp [doConCheck, hl, buildConv, evaluate_nil_list]

/-- The call `readAll []`. -/
theorem runs_readAll_call (E₁ Ec : SemEnv Value) (ℓ : Nat)
    (hbuf : nsLookup E₁.v (.short (ofString bufName)) = some (.loc true ℓ))
    (hcons : HasListCons E₁.c) (hcons' : HasListCons Ec.c)
    (hlk : nsLookup Ec.v (.short (ofString readAllName)) = some (readAllClosure E₁))
    (s : State Stdio) (inp : List (BitVec 8)) (c d : BitVec 8)
    (hst : s.refs[ℓ]? = some (.w8array [c, d])) (hor : s.ffi.oracle = stdioOracle)
    (hin : s.ffi.ffiState.input = inp) :
    ∃ refs' reads v,
      Runs s Ec [.app .opapp [var readAllName, .con (some (.short (ofString "[]"))) []]]
        { s with
          refs := refs'
          ffi := { s.ffi with ffiState := { input := [] }, ioEvents := s.ffi.ioEvents ++ reads } }
        (.val [v]) ∧
      LIST NAT (byteNats inp).reverse v ∧ (∀ e ∈ reads, IsRead e) ∧
      (∃ c' d', refs'[ℓ]? = some (.w8array [c', d'])) := by
  have hargs := Runs.cons (Runs.con_nil s hcons') (Runs.var s Ec readAllName _ hlk)
  have happ : doOpApp [readAllClosure E₁, .conv (some (.typeStamp nilC 1)) []] =
      some (recBodyEnv E₁ readAllFuns (ofString "acc") (.conv (some (.typeStamp nilC 1)) []),
        readAllBody) := by
    simp [doOpApp, readAllClosure, readAllFuns, findRecFun, recBodyEnv]
  obtain ⟨refs', reads, v, heval, hv, hreads, hbuf'⟩ :=
    readAll_spec E₁ ℓ hbuf hcons inp [] _ rfl s c d hst hor hin 0
  refine ⟨refs', reads, v, Runs.app_opapp hargs happ ⟨inp.length + 0, 0, ?_⟩, by simpa using hv,
    hreads, hbuf'⟩
  rw [heval]

def writeExp : Exp :=
  .app (.ffi (ofString "write"))
    [.if_ (var resultName) (.lit (.strLit (ofString "accepted\n"))) (.lit (.strLit (ofString "rejected\n"))),
     var bufName]

theorem writeExp_eq (entryName revName : String) :
    (mainDecs entryName revName)[3]? = some (.dlet Flapjack.Misc.Location.unknownLoc .pany writeExp) := rfl

/-- The `write` event for a verdict. -/
def writeEvent (b : Bool) (c d : BitVec 8) : HolIoEvent :=
  { name := .extCall (ofString "write"), configuration := verdictBytes b, bytes := [(c, c), (d, d)] }

theorem eval_write (env : SemEnv Value) (ℓ : Nat)
    (hbuf : nsLookup env.v (.short (ofString bufName)) = some (.loc true ℓ)) (b : Bool)
    (hres : nsLookup env.v (.short (ofString resultName)) = some (boolValue b))
    (s : State Stdio) (c d : BitVec 8) (hst : s.refs[ℓ]? = some (.w8array [c, d]))
    (hor : s.ffi.oracle = stdioOracle) :
    evaluate s env [writeExp] =
      ({ s with
          refs := s.refs.set ℓ (.w8array [c, d])
          ffi := { s.ffi with ioEvents := s.ffi.ioEvents ++ [writeEvent b c d] } },
        .val [.conv none []]) := by
  have hif : evaluate s env [.if_ (var resultName) (.lit (.strLit (ofString "accepted\n")))
      (.lit (.strLit (ofString "rejected\n")))] =
      (s, .val [.litv (.strLit (if b then ofString "accepted\n" else ofString "rejected\n"))]) := by
    rw [evaluate_if_val (s₁ := s) (b := b) (by simp [var, evaluate, hres])]
    cases b <;> simp [evaluate]
  have hargs := evaluate_cons_val (by simp [var, evaluate, hbuf] :
    evaluate s env [var bufName] = (s, .val [.loc true ℓ])) hif
  have hdo : doApp (s.refs, s.ffi) (.ffi (ofString "write"))
      [.litv (.strLit (if b then ofString "accepted\n" else ofString "rejected\n")), .loc true ℓ] =
      some ((s.refs.set ℓ (.w8array [c, d]),
        { s.ffi with ioEvents := s.ffi.ioEvents ++ [writeEvent b c d] }), .val (.conv none [])) := by
    rcases hf : s.ffi with ⟨o, st, evs⟩
    rw [hf] at hor
    simp only at hor
    subst hor
    cases b <;> simp +decide [doApp, doAppNumericCore, doAppBasic, storeLookup, storeAssign,
      callFFIHOL, hst, stdioOracle, storeValueSameType, writeEvent, verdictBytes]
  have := evaluate_app_simple (op := .ffi (ofString "write"))
    (args := [.if_ (var resultName) (.lit (.strLit (ofString "accepted\n")))
      (.lit (.strLit (ofString "rejected\n"))), var bufName]) (by simpa using hargs) rfl (by simpa using hdo)
  simpa [writeExp, listResult] using this

/-! ## The whole main program -/

theorem conOk_alloc : conOk [] (.app .aw8alloc [.lit (.intLit 2), .lit (.word8 0)]) = true := by decide

theorem everyExp_readAll (envC : Namespace ModN ConN (Nat × Stamp)) (hc : HasListCons envC) :
    readAllFuns.all (fun (_, _, e) => everyExp (oneConCheck envC) e) = true := by
  have ht : TableOk [(ofString "::", 2)] envC := by
    intro c n h
    simp only [List.lookup] at h
    split at h
    · next heq => cases h; rw [beq_iff_eq] at heq; subst heq; exact ⟨_, hc.cons⟩
    · simp at h
  have hk : conOk [(ofString "::", 2)] readAllBody = true := by decide
  simp [readAllFuns, everyExp_of_conOk ht _ hk]

theorem everyExp_main3 (envC : Namespace ModN ConN (Nat × Stamp)) (hc : HasListCons envC)
    (entryName revName : String) :
    everyExp (oneConCheck envC)
      (.app .opapp [var entryName,
       .app .opapp [var revName,
         .con none [.app .opapp [var readAllName, .con (some (.short (ofString "[]"))) []],
           .con (some (.short (ofString "[]"))) []]]]) = true := by
  have ht : TableOk [(ofString "[]", 0)] envC := by
    intro c n h
    simp only [List.lookup] at h
    split at h
    · next heq => cases h; rw [beq_iff_eq] at heq; subst heq; exact ⟨_, hc.nil⟩
    · simp at h
  apply everyExp_of_conOk ht
  simp [conOk, conOkList, conHeadOk, var]

theorem everyExp_write (envC : Namespace ModN ConN (Nat × Stamp)) :
    everyExp (oneConCheck envC) writeExp = true :=
  everyExp_of_conOk (tbl := []) (fun _ _ h => by simp at h) _ (by decide)

theorem lookup_extend_miss (l : List (VarN × Value)) (env : SemEnv Value) (n : VarN)
    (h : ∀ x, (n, x) ∉ l) :
    nsLookup (extendDecEnv { v := .bind l [], c := nsEmpty } env).v (.short n) = nsLookup env.v (.short n) := by
  obtain ⟨⟨vs, ms⟩, c⟩ := env
  simp only [extendDecEnv, nsAppend, nsLookup_bind_short]
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, x⟩ := p
    have hk : n ≠ k := fun e => h x (by simp [e])
    have : (n == k) = false := beq_eq_false_iff_ne.mpr hk
    simp only [List.cons_append, List.lookup, this]
    exact ih (fun x hx => h x (.tail _ hx))

theorem lookup_extend_hit (k : VarN) (x : Value) (l : List (VarN × Value)) (env : SemEnv Value) :
    nsLookup (extendDecEnv { v := .bind ((k, x) :: l) [], c := nsEmpty } env).v (.short k) = some x := by
  obtain ⟨⟨vs, ms⟩, c⟩ := env
  simp [extendDecEnv, nsAppend, nsLookup_bind_short, List.lookup]

theorem extend_c (l : List (VarN × Value)) (env : SemEnv Value) :
    (extendDecEnv { v := .bind l [], c := nsEmpty } env).c = nsAppend nsEmpty env.c := by
  simp [extendDecEnv]

theorem nsAppend_nsEmpty (e : Namespace ModN ConN (Nat × Stamp)) : nsAppend nsEmpty e = e := by
  cases e; rfl

/-- The third main declaration: `result = entry (revApp (readAll [], []))`. -/
theorem runs_main3 (entryName revName : String) (entry : List Nat → Bool) (E₁ E₂ : SemEnv Value)
    (ℓ : Nat) (ve vr : Value)
    (hbuf : nsLookup E₁.v (.short (ofString bufName)) = some (.loc true ℓ))
    (hc₁ : HasListCons E₁.c) (hc₂ : HasListCons E₂.c)
    (hlk : nsLookup E₂.v (.short (ofString readAllName)) = some (readAllClosure E₁))
    (hentry : nsLookup E₂.v (.short (ofString entryName)) = some ve) (he : Arrow (LIST NAT) BOOL entry ve)
    (hrev : nsLookup E₂.v (.short (ofString revName)) = some vr)
    (hr : Arrow (PAIR (LIST NAT) (LIST NAT)) (LIST NAT) revApp.cake_tupled vr)
    (s : State Stdio) (input : List (BitVec 8)) (c d : BitVec 8)
    (hst : s.refs[ℓ]? = some (.w8array [c, d])) (hor : s.ffi.oracle = stdioOracle)
    (hin : s.ffi.ffiState.input = input) :
    ∃ refs' reads,
      Runs s E₂ [.app .opapp [var entryName,
       .app .opapp [var revName,
         .con none [.app .opapp [var readAllName, .con (some (.short (ofString "[]"))) []],
           .con (some (.short (ofString "[]"))) []]]]]
        { s with
          refs := refs'
          ffi := { s.ffi with ffiState := { input := [] }, ioEvents := s.ffi.ioEvents ++ reads } }
        (.val [boolValue (entry (byteNats input))]) ∧
      (∀ e ∈ reads, IsRead e) ∧ (∃ c' d', refs'[ℓ]? = some (.w8array [c', d'])) := by
  obtain ⟨refs₁, reads, v, hrun, hv, hreads, c₁, d₁, hbuf₁⟩ :=
    runs_readAll_call E₁ E₂ ℓ hbuf hc₁ hc₂ hlk s input c d hst hor hin
  let s₁ : State Stdio := { s with
    refs := refs₁
    ffi := { s.ffi with ffiState := { input := [] }, ioEvents := s.ffi.ioEvents ++ reads } }
  -- the pair (readAll [], [])
  have hpair := Runs.con_none (args := [.app .opapp [var readAllName, .con (some (.short (ofString "[]"))) []],
      .con (some (.short (ofString "[]"))) []])
    (Runs.cons (Runs.con_nil s hc₂) hrun)
  -- revApp (…)
  obtain ⟨vrev, rr, hrevRun, hvrev⟩ := Runs.app_returns
    (Runs.cons hpair (Runs.var s₁ E₂ revName vr hrev))
    (hr ((byteNats input).reverse, []) _ ⟨v, _, hv, rfl, rfl⟩)
  -- entry (…)
  let s₂ : State Stdio := { s₁ with refs := s₁.refs ++ rr }
  obtain ⟨vb, re, hentryRun, hvb⟩ := Runs.app_returns
    (Runs.cons hrevRun (Runs.var s₂ E₂ entryName ve hentry)) (he _ vrev hvrev)
  refine ⟨refs₁ ++ rr ++ re, reads, ?_, hreads, c₁, d₁, ?_⟩
  · have hb : vb = boolValue (entry (byteNats input)) := by
      simpa [BOOL, revApp_eq, byteNats, revApp.cake_tupled] using hvb
    subst hb
    exact hentryRun
  · have hlt : ℓ < refs₁.length := by
      rcases Nat.lt_or_ge ℓ refs₁.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hbuf₁
    rw [List.append_assoc, List.getElem?_append_left hlt, hbuf₁]

/-- **The main program.** In an environment binding `entry` and `revApp` to
values satisfying their certificates, the main declarations run and add
only `read` events and one `write` of `entry`'s verdict on the input. -/
theorem mainRun (entryName revName : String) (entry : List Nat → Bool) (E : SemEnv Value)
    (ve vr : Value)
    (hentry : nsLookup E.v (.short (ofString entryName)) = some ve) (he : Arrow (LIST NAT) BOOL entry ve)
    (hrev : nsLookup E.v (.short (ofString revName)) = some vr)
    (hr : Arrow (PAIR (LIST NAT) (LIST NAT)) (LIST NAT) revApp.cake_tupled vr)
    (hlist : HasListCons E.c)
    (hn₁ : ofString entryName ≠ ofString bufName) (hn₂ : ofString entryName ≠ ofString readAllName)
    (hn₃ : ofString revName ≠ ofString bufName) (hn₄ : ofString revName ≠ ofString readAllName)
    (s : State Stdio) (hor : s.ffi.oracle = stdioOracle) (input : List (BitVec 8))
    (hin : s.ffi.ffiState.input = input) :
    ∃ s' envM reads c d, DeclsRun s E (mainDecs entryName revName) s' envM ∧
      s'.ffi.ioEvents = s.ffi.ioEvents ++ reads ++ [writeEvent (entry (byteNats input)) c d] ∧
      (∀ e ∈ reads, IsRead e) := by
  -- 1. the buffer
  let ℓ := s.refs.length
  let s₁ : State Stdio := { s with refs := s.refs ++ [.w8array [0, 0]] }
  have hd₁ : DeclsRun s E [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString bufName))
      (.app .aw8alloc [.lit (.intLit 2), .lit (.word8 0)])] s₁
      { v := alistToNs [(ofString bufName, .loc true ℓ)], c := nsEmpty } :=
    DeclsRun.dlet (everyExp_of_conOk (tbl := []) (fun _ _ h => by simp at h) _ conOk_alloc)
      ⟨0, 0, eval_alloc { s with clock := 0 } E⟩
  let E₁ := extendDecEnv { v := .bind [(ofString bufName, .loc true ℓ)] [], c := nsEmpty } E
  have hc₁ : HasListCons E₁.c := by
    simpa [E₁, extend_c, nsAppend_nsEmpty] using hlist
  have hbuf₁ : nsLookup E₁.v (.short (ofString bufName)) = some (.loc true ℓ) :=
    lookup_extend_hit _ _ [] E
  -- 2. readAll
  have hd₂ : DeclsRun s₁ E₁ [.dletrec Flapjack.Misc.Location.unknownLoc readAllFuns] s₁
      { v := buildRecEnv readAllFuns E₁ nsEmpty, c := nsEmpty } :=
    DeclsRun.dletrec s₁ (by decide) (everyExp_readAll E₁.c hc₁)
  let E₂ := extendDecEnv { v := .bind [(ofString readAllName, readAllClosure E₁)] [], c := nsEmpty } E₁
  have hbre : buildRecEnv readAllFuns E₁ nsEmpty = .bind [(ofString readAllName, readAllClosure E₁)] [] := by
    simp [buildRecEnv, readAllFuns, readAllClosure, nsEmpty]
  have hc₂ : HasListCons E₂.c := by
    simpa [E₂, extend_c, nsAppend_nsEmpty] using hc₁
  have hlk₂ : nsLookup E₂.v (.short (ofString readAllName)) = some (readAllClosure E₁) :=
    lookup_extend_hit _ _ [] E₁
  have hentry₂ : nsLookup E₂.v (.short (ofString entryName)) = some ve := by
    rw [lookup_extend_miss _ _ _ (by simp [hn₂]), lookup_extend_miss _ _ _ (by simp [hn₁])]
    exact hentry
  have hrev₂ : nsLookup E₂.v (.short (ofString revName)) = some vr := by
    rw [lookup_extend_miss _ _ _ (by simp [hn₄]), lookup_extend_miss _ _ _ (by simp [hn₃])]
    exact hrev
  -- 3. result
  have hst₁ : s₁.refs[ℓ]? = some (.w8array [0, 0]) := by simp [s₁, ℓ]
  obtain ⟨refs₃, reads, hrun₃, hreads, c, d, hbuf₃⟩ :=
    runs_main3 entryName revName entry E₁ E₂ ℓ ve vr hbuf₁ hc₁ hc₂ hlk₂ hentry₂ he hrev₂ hr
      s₁ input 0 0 hst₁ hor hin
  let b := entry (byteNats input)
  let s₃ : State Stdio := { s₁ with
    refs := refs₃
    ffi := { s₁.ffi with ffiState := { input := [] }, ioEvents := s₁.ffi.ioEvents ++ reads } }
  have hd₃ := DeclsRun.dlet (loc := Flapjack.Misc.Location.unknownLoc) (x := ofString resultName)
    (everyExp_main3 E₂.c hc₂ entryName revName) hrun₃
  let E₃ := extendDecEnv { v := .bind [(ofString resultName, boolValue b)] [], c := nsEmpty } E₂
  have hres₃ : nsLookup E₃.v (.short (ofString resultName)) = some (boolValue b) :=
    lookup_extend_hit _ _ [] E₂
  have hbuf₃' : nsLookup E₃.v (.short (ofString bufName)) = some (.loc true ℓ) := by
    rw [lookup_extend_miss _ _ _ (by simp; decide), lookup_extend_miss _ _ _ (by simp; decide)]
    exact hbuf₁
  -- 4. write
  have hw := eval_write E₃ ℓ hbuf₃' b hres₃ { s₃ with clock := 0 } c d hbuf₃ hor
  let s₄ : State Stdio := { s₃ with
    refs := s₃.refs.set ℓ (.w8array [c, d])
    ffi := { s₃.ffi with ioEvents := s₃.ffi.ioEvents ++ [writeEvent b c d] } }
  have hd₄ := DeclsRun.dlet_any (loc := Flapjack.Misc.Location.unknownLoc) (s := s₃) (s₁ := s₄)
    (everyExp_write E₃.c) ⟨0, 0, hw⟩
  -- chain
  have hal : ∀ l : List (VarN × Value), (alistToNs l : Namespace ModN VarN Value) = .bind l [] := by
    intro l; simp [alistToNs]
  rw [hal] at hd₁ hd₃
  rw [hbre] at hd₂
  refine ⟨_, _, reads, c, d, DeclsRun.cons hd₁ (DeclsRun.cons hd₂ (DeclsRun.cons hd₃ hd₄)), ?_, hreads⟩
  simp only [s₄, s₃, s₁, b, List.append_assoc]

end ConPastel.Main
