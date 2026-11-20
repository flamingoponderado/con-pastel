import ConPastel.Translator.Lemmas

/-!
# The stateful refinement judgement (issue #30)

`Eval` (`ConPastel.Translator.Eval`) lets translated code only append to the
store, and its invariants are store-free. `EvalM` relates a CakeML expression
to a state-exception computation `StateT σ (Except ε) α` (con-leche's kernel
monad `CheckCM` is one), where the Lean state `σ` is held in a fixed set of
store cells it owns (`R.owns`), described by a store relation `R.rel` that
reads only those cells. From any store holding `st`, the expression runs to a store
holding the new state, changing only owned cells and appending elsewhere, with

* on success, a value representing the result;
* on an exception, a raised value representing the error (the state is then
  unconstrained: con-leche's kernel never catches its exceptions).

This is the Lean counterpart of HOL4 CakeML's `EvalM`
(`translator/monadic/ml_monad_translatorScript.sml`), with a plain store
relation and an explicit frame in place of separation logic.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL

/-- A Lean state held in store cells: `owns r l` says the state owns cell `l`
of store `r` (the owned cells may depend on the store: a resized table lives
in a newly allocated array). -/
structure StateRel (σ : Type) where
  owns : Store Value → Nat → Prop
  rel : σ → Store Value → Prop
  /-- The owned cells exist. -/
  inRange : ∀ st r, rel st r → ∀ l, owns r l → l < r.length
  /-- The relation reads only owned cells: it survives appends and changes elsewhere. -/
  stable : ∀ st r r', rel st r → r.length ≤ r'.length → (∀ l, owns r l → r'[l]? = r[l]?) →
    rel st r'
  /-- So does ownership of the old cells. -/
  ownsStable : ∀ st r r', rel st r → r.length ≤ r'.length → (∀ l, owns r l → r'[l]? = r[l]?) →
    ∀ l < r.length, owns r' l → owns r l

/-- `r'` extends `r`, agrees with it on the cells `r` does not own, and owns
no old cell that `r` did not (only new cells become owned). -/
def Frame {σ : Type} (R : StateRel σ) (r r' : Store Value) : Prop :=
  r.length ≤ r'.length ∧ (∀ l < r.length, ¬ R.owns r l → r'[l]? = r[l]?) ∧
    (∀ l < r.length, R.owns r' l → R.owns r l)

theorem Frame.refl {σ : Type} (R : StateRel σ) (r : Store Value) : Frame R r r :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl, fun _ _ h => h⟩

theorem Frame.trans {σ : Type} {R : StateRel σ} {r₁ r₂ r₃ : Store Value} (h₁ : Frame R r₁ r₂)
    (h₂ : Frame R r₂ r₃) : Frame R r₁ r₃ := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun l hl hn => ?_, fun l hl ho => ?_⟩
  · have hl₂ := Nat.lt_of_lt_of_le hl h₁.1
    rw [h₂.2.1 l hl₂ (fun ho₂ => hn (h₁.2.2 l hl ho₂)), h₁.2.1 l hl hn]
  · exact h₁.2.2 l hl (h₂.2.2 l (Nat.lt_of_lt_of_le hl h₁.1) ho)

/-- Appending cells: the owned cells are those of the prefix (`R.owns` reads the
store only through owned cells, which the append does not change). -/
theorem Frame.append {σ : Type} {R : StateRel σ} {st : σ} {r : Store Value} (hst : R.rel st r)
    (extra : Store Value) : Frame R r (r ++ extra) :=
  ⟨by simp, fun l hl _ => by simp [List.getElem?_append_left hl],
    R.ownsStable st r _ hst (by simp) (fun l hl => by
      simp [List.getElem?_append_left (R.inRange st r hst l hl)])⟩

theorem StateRel.rel_append {σ : Type} {R : StateRel σ} {st : σ} {r : Store Value} (hst : R.rel st r)
    (extra : Store Value) : R.rel st (r ++ extra) :=
  R.stable st _ _ hst (by simp) (fun l hl => by simp [List.getElem?_append_left (R.inRange st _ hst l hl)])

/-- The outcome of a monadic run, against the CakeML result and final store. -/
def MRes {σ ε α : Type} (R : StateRel σ) (A : RefInv α) (B : RefInv ε) :
    Except ε (α × σ) → Store Value → Result (List Value) Value → Prop
  | .ok (a, st'), refs, res => R.rel st' refs ∧ ∃ v, res = .val [v] ∧ A a v
  | .error x, _, res => ∃ v, res = .err (.raise v) ∧ B x v

/-- The stateful refinement judgement. -/
def EvalM {σ ε α : Type} (R : StateRel σ) (env : SemEnv Value) (e : Exp) (A : RefInv α)
    (B : RefInv ε) (f : StateT σ (Except ε) α) : Prop :=
  ∀ (τ : Type) (s : State τ) (st : σ), R.rel st s.refs →
    ∃ refs' res, Runs s env [e] { s with refs := refs' } res ∧ Frame R s.refs refs' ∧
      MRes R A B (f st) refs' res

/-! ## Pure code -/

/-- Pure code (`Eval`) is monadic code that returns its value and keeps the state. -/
theorem EvalM_pure {σ ε α : Type} {R : StateRel σ} {env : SemEnv Value} {e : Exp} {A : RefInv α}
    {B : RefInv ε} {a : α} (h : Eval env e (A a)) : EvalM R env e A B (pure a) := by
  intro τ s st hst
  obtain ⟨v, extra, hv, hA⟩ := h τ s
  exact ⟨s.refs ++ extra, .val [v], hv.runs, Frame.append hst _, StateRel.rel_append hst _, v, rfl, hA⟩

/-! ## `bind` as `let` -/

theorem evaluate_let_err {τ : Type} {s s₁ : State τ} {env : SemEnv Value} {n : Option VarN}
    {e₁ e₂ : Exp} {err : ErrorResult Value} (h₁ : evaluate s env [e₁] = (s₁, .err err)) :
    evaluate s env [.let_ n e₁ e₂] = (s₁, .err err) := by
  have hfix : fixClock s (s₁, (Result.err err : Result (List Value) Value)) = (s₁, .err err) := by
    rw [← h₁]; exact fixClock_evaluate s env _
  rw [evaluate]
  simp [h₁, hfix]

theorem Runs.let_err {τ : Type} {s s₁ : State τ} {env : SemEnv Value} {n : Option VarN}
    {e₁ e₂ : Exp} {v : Value} (h₁ : Runs s env [e₁] s₁ (.err (.raise v))) :
    Runs s env [.let_ n e₁ e₂] s₁ (.err (.raise v)) := by
  obtain ⟨a₁, a₂, ha⟩ := h₁
  exact ⟨a₁, a₂, evaluate_let_err ha⟩

theorem MRes.not_timeout {σ ε α : Type} {R : StateRel σ} {A : RefInv α} {B : RefInv ε}
    {x : Except ε (α × σ)} {refs : Store Value} {res : Result (List Value) Value}
    (h : MRes R A B x refs res) : res ≠ .err (.abort .timeoutError) := by
  cases x with
  | ok p => obtain ⟨a, st⟩ := p; obtain ⟨_, v, hv, _⟩ := h; subst hv; simp
  | error e => obtain ⟨v, hv, _⟩ := h; subst hv; simp

theorem EvalM_bind {σ ε α β : Type} {R : StateRel σ} {env : SemEnv Value} {n : VarN}
    {e₁ e₂ : Exp} {A : RefInv α} {C : RefInv β} {B : RefInv ε}
    {f : StateT σ (Except ε) α} {g : α → StateT σ (Except ε) β}
    (h₁ : EvalM R env e₁ A B f)
    (h₂ : ∀ a v, A a v → EvalM R { env with v := nsOptBind (some n) v env.v } e₂ C B (g a)) :
    EvalM R env (.let_ (some n) e₁ e₂) C B (f >>= g) := by
  intro τ s st hst
  obtain ⟨refs₁, res₁, hr₁, hf₁, hm₁⟩ := h₁ τ s st hst
  have hb : (f >>= g) st = match f st with
      | .ok (a, st') => g a st'
      | .error x => .error x := by
    show (f st >>= fun p => g p.1 p.2) = _
    cases f st <;> rfl
  rw [hb]
  revert hm₁
  cases f st with
  | error x =>
    intro hm₁
    obtain ⟨v, hv, hB⟩ := hm₁; subst hv
    exact ⟨refs₁, _, Runs.let_err hr₁, hf₁, v, rfl, hB⟩
  | ok p =>
    obtain ⟨a, st₁⟩ := p
    intro hm₁
    obtain ⟨hst₁, v, hv, hA⟩ := hm₁; subst hv
    obtain ⟨refs₂, res₂, hr₂, hf₂, hm₂⟩ := h₂ a v hA τ { s with refs := refs₁ } st₁ hst₁
    refine ⟨refs₂, res₂, ?_, hf₁.trans hf₂, hm₂⟩
    have := Runs.let_ (n := some n) hr₁ hr₂ hm₂.not_timeout
    simpa using this

/-! ## Exceptions -/

theorem Runs.raise {τ : Type} {s s₁ : State τ} {env : SemEnv Value} {e : Exp} {v : Value}
    (h : Runs s env [e] s₁ (.val [v])) : Runs s env [.raise e] s₁ (.err (.raise v)) := by
  obtain ⟨a₁, a₂, ha⟩ := h
  refine ⟨a₁, a₂, ?_⟩
  have hfix : fixClock { s with clock := a₁ } ({ s₁ with clock := a₂ }, (Result.val [v] : Result (List Value) Value)) =
      ({ s₁ with clock := a₂ }, .val [v]) := by
    rw [← ha]; exact fixClock_evaluate _ env _
  rw [evaluate]
  simp [ha, headValue, Flapjack.holHd]

theorem EvalM_throw {σ ε α : Type} {R : StateRel σ} {env : SemEnv Value} {e : Exp} {A : RefInv α}
    {B : RefInv ε} {x : ε} (h : Eval env e (B x)) :
    EvalM R env (.raise e) A B (throw x) := by
  intro τ s st hst
  obtain ⟨v, extra, hv, hB⟩ := h τ s
  exact ⟨s.refs ++ extra, _, Runs.raise hv.runs, Frame.append hst _, v, rfl, hB⟩

/-! ## A state in one reference cell -/

/-- The state is the contents of the reference cell `loc`, represented by `S`. -/
def refRel {σ : Type} (S : RefInv σ) (loc : Nat) : StateRel σ where
  owns _ l := l = loc
  rel st r := ∃ v, r[loc]? = some (.refv v) ∧ S st v
  inRange st r h l hl := by
    obtain ⟨v, hv, _⟩ := h
    subst hl
    exact (List.getElem?_eq_some_iff.mp hv).1
  stable st r r' h _ hsame := by
    obtain ⟨v, hv, hS⟩ := h
    exact ⟨v, by rw [hsame loc rfl, hv], hS⟩
  ownsStable _ _ _ _ _ _ _ _ h := h

/-- `!r`: the state. -/
theorem EvalM_get {σ ε : Type} {S : RefInv σ} {loc : Nat} {env : SemEnv Value} {r : Ident ModN VarN}
    {B : RefInv ε} {b : Bool} (hr : nsLookup env.v r = some (.loc b loc)) :
    EvalM (refRel S loc) env (.app .opderef [.var r]) S B get := by
  intro τ s st hst
  obtain ⟨v, hv, hS⟩ := hst
  refine ⟨s.refs, .val [v], ⟨0, 0, ?_⟩, Frame.refl _ _, ⟨v, hv, hS⟩, v, rfl, hS⟩
  have := evaluate_app_simple (s := { s with clock := 0 }) (s₁ := { s with clock := 0 }) (env := env)
    (op := .opderef) (args := [.var r]) (vs := [.loc b loc]) (refs := s.refs) (ffi := s.ffi) (r := .val v)
    (by simp [evaluate, hr]) rfl (by simp [doApp, doAppBasic, doAppNumericCore, storeLookup, hv])
  simpa [listResult] using this

/-- `r := e`: replace the state. -/
theorem EvalM_set {σ ε : Type} {S : RefInv σ} {loc : Nat} {env : SemEnv Value} {r : Ident ModN VarN}
    {e : Exp} {B : RefInv ε} {b : Bool} {st' : σ} (hr : nsLookup env.v r = some (.loc b loc))
    (he : Eval env e (S st')) :
    EvalM (refRel S loc) env (.app .opassign [.var r, e]) UNIT B (set st') := by
  intro τ s st hst
  obtain ⟨v₀, hv₀, _⟩ := hst
  obtain ⟨w, extra, hw, hS⟩ := he τ s
  obtain ⟨a₁, a₂, ha⟩ := hw.runs
  have hlt : loc < s.refs.length := (List.getElem?_eq_some_iff.mp hv₀).1
  let refs₁ := s.refs ++ extra
  have hv₁ : refs₁[loc]? = some (.refv v₀) := by simp [refs₁, List.getElem?_append_left hlt, hv₀]
  refine ⟨refs₁.set loc (.refv w), .val [.conv none []], ⟨a₁, a₂, ?_⟩, ⟨by simp [refs₁], ?_, fun _ _ h => h⟩, ?_⟩
  · have hargs : evaluate { s with clock := a₁ } env [e, .var r] =
        ({ s with refs := refs₁, clock := a₂ }, .val [w, .loc b loc]) := by
      have h2 : evaluate { s with refs := refs₁, clock := a₂ } env [.var r] =
          ({ s with refs := refs₁, clock := a₂ }, .val [.loc b loc]) := by simp [evaluate, hr]
      exact evaluate_cons_val ha h2
    have := evaluate_app_simple (s := { s with clock := a₁ }) (s₁ := { s with refs := refs₁, clock := a₂ })
      (env := env) (op := .opassign) (args := [.var r, e]) (vs := [w, .loc b loc])
      (refs := refs₁.set loc (.refv w)) (ffi := s.ffi) (r := .val (.conv none []))
      (by simpa using hargs) rfl
      (by simp [doApp, doAppBasic, doAppNumericCore, storeAssign, hv₁, storeValueSameType])
    simpa [listResult] using this
  · intro l hl hn
    have hne : l ≠ loc := fun h => hn h
    simp [refs₁, List.getElem?_set_ne (Ne.symm hne), List.getElem?_append_left hl]
  · have hl₁ : loc < refs₁.length := by simp [refs₁]; omega
    refine ⟨⟨w, ?_, hS⟩, _, rfl, ?_⟩
    · show (refs₁.set loc (.refv w))[loc]? = some (.refv w)
      rw [List.getElem?_set_self hl₁]
    · rfl

/-! ## A state in a CakeML array (`Array.array`) -/

/-- The state is a Lean array held in the CakeML array cell `aloc`: one
CakeML value per element, each represented by `A`. -/
def arrRel {α : Type} (A : RefInv α) (aloc : Nat) : StateRel (Array α) where
  owns _ l := l = aloc
  rel st r := ∃ vs, r[aloc]? = some (.varray vs) ∧ List.Forall₂ A st.toList vs
  inRange st r h l hl := by
    obtain ⟨vs, hv, _⟩ := h
    subst hl
    exact (List.getElem?_eq_some_iff.mp hv).1
  stable st r r' h _ hsame := by
    obtain ⟨vs, hv, hA⟩ := h
    exact ⟨vs, by rw [hsame aloc rfl, hv], hA⟩
  ownsStable _ _ _ _ _ _ _ _ h := h

/-- `Array.length arr`. -/
theorem Runs.alength {τ : Type} {s : State τ} {env : SemEnv Value} {arr : Ident ModN VarN}
    {b : Bool} {aloc : Nat} {vs : List Value} (harr : nsLookup env.v arr = some (.loc b aloc))
    (hv : s.refs[aloc]? = some (.varray vs)) :
    Runs s env [.app .alength [.var arr]] s (.val [.litv (.intLit vs.length)]) := by
  refine ⟨s.clock, s.clock, ?_⟩
  have := evaluate_app_simple (s := { s with clock := s.clock }) (s₁ := { s with clock := s.clock })
    (env := env) (op := .alength) (args := [.var arr]) (vs := [.loc b aloc]) (refs := s.refs)
    (ffi := s.ffi) (r := .val (.litv (.intLit vs.length)))
    (by simp [evaluate, harr]) rfl (by simp [doApp, doAppBasic, doAppNumericCore, storeLookup, hv])
  simpa [listResult] using this

/-- `Array.sub arr i`, in range. -/
theorem Runs.asub {τ : Type} {s : State τ} {env : SemEnv Value} {arr ix : Ident ModN VarN}
    {b : Bool} {aloc i : Nat} {vs : List Value} (harr : nsLookup env.v arr = some (.loc b aloc))
    (hix : nsLookup env.v ix = some (.litv (.intLit i))) (hv : s.refs[aloc]? = some (.varray vs))
    (hi : i < vs.length) :
    Runs s env [.app .asub [.var arr, .var ix]] s (.val [vs[i]]) := by
  refine ⟨s.clock, s.clock, ?_⟩
  have hargs : evaluate { s with clock := s.clock } env [.var ix, .var arr] =
      ({ s with clock := s.clock }, .val [.litv (.intLit i), .loc b aloc]) :=
    evaluate_cons_val (s₁ := { s with clock := s.clock }) (by simp [evaluate, hix]) (by simp [evaluate, harr])
  have := evaluate_app_simple (s := { s with clock := s.clock }) (s₁ := { s with clock := s.clock })
    (env := env) (op := .asub) (args := [.var arr, .var ix]) (vs := [.litv (.intLit i), .loc b aloc])
    (refs := s.refs) (ffi := s.ffi) (r := .val vs[i])
    (by simpa using hargs) rfl
    (by
      have hneg : ¬ ((i : Int) < 0) := by omega
      simp [doApp, doAppBasic, doAppNumericCore, storeLookup, hv, readIndexed, hneg,
        List.getElem?_eq_getElem hi])
  simpa [listResult] using this

/-- `Array.update arr i x`, in range: the cell is updated in place. -/
theorem Runs.aupdate {τ : Type} {s : State τ} {env : SemEnv Value} {arr ix xv : Ident ModN VarN}
    {b : Bool} {aloc i : Nat} {vs : List Value} {x : Value}
    (harr : nsLookup env.v arr = some (.loc b aloc))
    (hix : nsLookup env.v ix = some (.litv (.intLit i))) (hx : nsLookup env.v xv = some x)
    (hv : s.refs[aloc]? = some (.varray vs)) (hi : i < vs.length) :
    Runs s env [.app .aupdate [.var arr, .var ix, .var xv]]
      { s with refs := s.refs.set aloc (.varray (vs.set i x)) } (.val [.conv none []]) := by
  refine ⟨s.clock, s.clock, ?_⟩
  have hargs : evaluate { s with clock := s.clock } env [.var xv, .var ix, .var arr] =
      ({ s with clock := s.clock }, .val [x, .litv (.intLit i), .loc b aloc]) :=
    evaluate_cons_val (s₁ := { s with clock := s.clock }) (by simp [evaluate, hx])
      (evaluate_cons_val (s₁ := { s with clock := s.clock }) (by simp [evaluate, hix]) (by simp [evaluate, harr]))
  have := evaluate_app_simple (s := { s with clock := s.clock }) (s₁ := { s with clock := s.clock })
    (env := env) (op := .aupdate) (args := [.var arr, .var ix, .var xv])
    (vs := [x, .litv (.intLit i), .loc b aloc]) (refs := s.refs.set aloc (.varray (vs.set i x)))
    (ffi := s.ffi) (r := .val (.conv none []))
    (by simpa using hargs) rfl
    (by
      have hneg : ¬ ((i : Int) < 0) := by omega
      have hle : ¬ (vs.length ≤ i) := by omega
      simp [doApp, doAppBasic, doAppNumericCore, storeLookup, hv, updateIndexed, hneg, hle,
        storeAssign, storeValueSameType])
  simpa [listResult] using this

/-! ### Element-wise representation -/

theorem forall₂_length {α : Type} {A : RefInv α} :
    ∀ {l : List α} {vs : List Value}, List.Forall₂ A l vs → l.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [forall₂_length h]

theorem forall₂_get {α : Type} {A : RefInv α} :
    ∀ {l : List α} {vs : List Value} (h : List.Forall₂ A l vs) (i : Nat) (hi : i < l.length),
      A l[i] (vs[i]'(forall₂_length h ▸ hi))
  | _ :: _, _ :: _, .cons ha _, 0, _ => ha
  | _ :: _, _ :: _, .cons _ h, i + 1, hi => forall₂_get h i (by simpa using hi)

theorem forall₂_set {α : Type} {A : RefInv α} {x : α} {xv : Value} (hx : A x xv) :
    ∀ {l : List α} {vs : List Value}, List.Forall₂ A l vs → ∀ i, List.Forall₂ A (l.set i x) (vs.set i xv)
  | [], [], _, _ => by simp
  | _ :: _, _ :: _, .cons ha h, 0 => by simp; exact ⟨hx, h⟩
  | _ :: _, _ :: _, .cons ha h, i + 1 => by simp; exact ⟨ha, forall₂_set hx h i⟩

/-! ### Evaluation equations -/

theorem evaluate_alength {τ : Type} (s : State τ) {env : SemEnv Value} {arr : Ident ModN VarN}
    {b : Bool} {aloc : Nat} {vs : List Value} (harr : nsLookup env.v arr = some (.loc b aloc))
    (hv : s.refs[aloc]? = some (.varray vs)) :
    evaluate s env [.app .alength [.var arr]] = (s, .val [.litv (.intLit vs.length)]) := by
  have := evaluate_app_simple (s := s) (s₁ := s) (env := env) (op := .alength) (args := [.var arr])
    (vs := [.loc b aloc]) (refs := s.refs) (ffi := s.ffi) (r := .val (.litv (.intLit vs.length)))
    (by simp [evaluate, harr]) rfl (by simp [doApp, doAppBasic, doAppNumericCore, storeLookup, hv])
  simpa [listResult] using this

/-- The bounds test `i < Array.length arr`. -/
theorem evaluate_ltLen {τ : Type} (s : State τ) {env : SemEnv Value} {arr ix : Ident ModN VarN}
    {b : Bool} {aloc i : Nat} {vs : List Value} (harr : nsLookup env.v arr = some (.loc b aloc))
    (hix : nsLookup env.v ix = some (.litv (.intLit i))) (hv : s.refs[aloc]? = some (.varray vs)) :
    evaluate s env [.app (.test (.compare .lt) .intT) [.var ix, .app .alength [.var arr]]] =
      (s, .val [boolValue (decide (i < vs.length))]) := by
  have hargs : evaluate s env [.app .alength [.var arr], .var ix] =
      (s, .val [.litv (.intLit vs.length), .litv (.intLit i)]) :=
    evaluate_cons_val (evaluate_alength s harr hv) (by simp [evaluate, hix])
  have := evaluate_app_simple (s := s) (s₁ := s) (env := env) (op := .test (.compare .lt) .intT)
    (args := [.var ix, .app .alength [.var arr]]) (vs := [.litv (.intLit vs.length), .litv (.intLit i)])
    (refs := s.refs) (ffi := s.ffi) (r := .val (boolValue (decide (i < vs.length))))
    (by simpa using hargs) rfl
    (by simp [doApp, doAppBasic, doAppNumericCore, doTest, (intCmp_spec _ _).1])
  simpa [listResult] using this

theorem evaluate_asub {τ : Type} (s : State τ) {env : SemEnv Value} {arr ix : Ident ModN VarN}
    {b : Bool} {aloc i : Nat} {vs : List Value} (harr : nsLookup env.v arr = some (.loc b aloc))
    (hix : nsLookup env.v ix = some (.litv (.intLit i))) (hv : s.refs[aloc]? = some (.varray vs))
    (hi : i < vs.length) :
    evaluate s env [.app .asub [.var arr, .var ix]] = (s, .val [vs[i]]) := by
  have hargs : evaluate s env [.var ix, .var arr] = (s, .val [.litv (.intLit i), .loc b aloc]) :=
    evaluate_cons_val (s₁ := s) (by simp [evaluate, hix]) (by simp [evaluate, harr])
  have := evaluate_app_simple (s := s) (s₁ := s) (env := env) (op := .asub) (args := [.var arr, .var ix])
    (vs := [.litv (.intLit i), .loc b aloc]) (refs := s.refs) (ffi := s.ffi) (r := .val vs[i])
    (by simpa using hargs) rfl
    (by
      have hneg : ¬ ((i : Int) < 0) := by omega
      simp [doApp, doAppBasic, doAppNumericCore, storeLookup, hv, readIndexed, hneg,
        List.getElem?_eq_getElem hi])
  simpa [listResult] using this

theorem evaluate_aupdate {τ : Type} (s : State τ) {env : SemEnv Value} {arr ix xv : Ident ModN VarN}
    {b : Bool} {aloc i : Nat} {vs : List Value} {x : Value}
    (harr : nsLookup env.v arr = some (.loc b aloc))
    (hix : nsLookup env.v ix = some (.litv (.intLit i))) (hx : nsLookup env.v xv = some x)
    (hv : s.refs[aloc]? = some (.varray vs)) (hi : i < vs.length) :
    evaluate s env [.app .aupdate [.var arr, .var ix, .var xv]] =
      ({ s with refs := s.refs.set aloc (.varray (vs.set i x)) }, .val [.conv none []]) := by
  have hargs : evaluate s env [.var xv, .var ix, .var arr] = (s, .val [x, .litv (.intLit i), .loc b aloc]) :=
    evaluate_cons_val (s₁ := s) (by simp [evaluate, hx])
      (evaluate_cons_val (s₁ := s) (by simp [evaluate, hix]) (by simp [evaluate, harr]))
  have := evaluate_app_simple (s := s) (s₁ := s) (env := env) (op := .aupdate)
    (args := [.var arr, .var ix, .var xv]) (vs := [x, .litv (.intLit i), .loc b aloc])
    (refs := s.refs.set aloc (.varray (vs.set i x))) (ffi := s.ffi) (r := .val (.conv none []))
    (by simpa using hargs) rfl
    (by
      have hneg : ¬ ((i : Int) < 0) := by omega
      have hle : ¬ (vs.length ≤ i) := by omega
      simp [doApp, doAppBasic, doAppNumericCore, storeLookup, hv, updateIndexed, hneg, hle,
        storeAssign, storeValueSameType])
  simpa [listResult] using this

/-- The bounds test `i < Array.length arr`, as an expression. -/
def ltLen (ix arr : Ident ModN VarN) : Exp :=
  .app (.test (.compare .lt) .intT) [.var ix, .app .alength [.var arr]]

/-- A guarded read from the array state: `Array.getD`. -/
theorem EvalM_arrGetD {α ε : Type} {A : RefInv α} {aloc : Nat} {env : SemEnv Value}
    {arr ix : Ident ModN VarN} {b : Bool} {i : Nat} {B : RefInv ε} {ed : Exp} {d : α}
    (harr : nsLookup env.v arr = some (.loc b aloc)) (hix : nsLookup env.v ix = some (.litv (.intLit i)))
    (hd : Eval env ed (A d)) :
    EvalM (arrRel A aloc) env (.if_ (ltLen ix arr) (.app .asub [.var arr, .var ix]) ed) A B
      (fun st => Except.ok (st.getD i d, st)) := by
  intro τ s st hst
  obtain ⟨vs, hv, hF⟩ := hst
  have hst : (arrRel A aloc).rel st s.refs := ⟨vs, hv, hF⟩
  have hlen := forall₂_length hF
  have hsz : st.size = vs.length := by rw [← Array.length_toList, hlen]
  unfold ltLen
  by_cases hi : i < vs.length
  · have hi' : i < st.size := by rw [hsz]; exact hi
    refine ⟨s.refs, .val [vs[i]], ⟨s.clock, s.clock, ?_⟩, Frame.refl _ _, hst, vs[i], rfl, ?_⟩
    · rw [evaluate_if_val (evaluate_ltLen _ harr hix (by simpa using hv))]
      simp only [decide_eq_true hi, if_true]
      exact evaluate_asub _ harr hix (by simpa using hv) hi
    · have := forall₂_get hF i (by simpa using hi')
      simpa [Array.getD, hi', Array.getElem_toList] using this
  · obtain ⟨v, extra, ⟨ck₁, ck₂, hev⟩, hA⟩ := hd τ s
    refine ⟨s.refs ++ extra, .val [v], ⟨ck₁, ck₂, ?_⟩, Frame.append hst _,
      StateRel.rel_append hst _, v, rfl, ?_⟩
    · rw [evaluate_if_val (evaluate_ltLen _ harr hix (by simpa using hv))]
      simp only [decide_eq_false hi, Bool.false_eq_true, if_false]
      exact hev
    · have hi' : ¬ i < st.size := by rw [hsz]; exact hi
      simpa [Array.getD, hi'] using hA

/-- A guarded in-place write to the array state: `Array.setIfInBounds`. -/
theorem EvalM_arrSet {α ε : Type} {A : RefInv α} {aloc : Nat} {env : SemEnv Value}
    {arr ix xv : Ident ModN VarN} {b : Bool} {i : Nat} {B : RefInv ε} {x : Value} {y : α}
    (harr : nsLookup env.v arr = some (.loc b aloc)) (hix : nsLookup env.v ix = some (.litv (.intLit i)))
    (hx : nsLookup env.v xv = some x) (hy : A y x) :
    EvalM (arrRel A aloc) env
      (.if_ (ltLen ix arr) (.app .aupdate [.var arr, .var ix, .var xv]) (.con none [])) UNIT B
      (fun st => Except.ok ((), st.setIfInBounds i y)) := by
  intro τ s st hst
  obtain ⟨vs, hv, hF⟩ := hst
  have hst : (arrRel A aloc).rel st s.refs := ⟨vs, hv, hF⟩
  have hlen := forall₂_length hF
  have hsz : st.size = vs.length := by rw [← Array.length_toList, hlen]
  have hlt : aloc < s.refs.length := (List.getElem?_eq_some_iff.mp hv).1
  unfold ltLen
  by_cases hi : i < vs.length
  · have hrel : (arrRel A aloc).rel (st.setIfInBounds i y) (s.refs.set aloc (.varray (vs.set i x))) :=
      ⟨vs.set i x, List.getElem?_set_self hlt, by simpa [Array.toList_setIfInBounds] using forall₂_set hy hF i⟩
    refine ⟨s.refs.set aloc (.varray (vs.set i x)), .val [.conv none []], ⟨s.clock, s.clock, ?_⟩,
      ⟨by simp, fun l _ hn => List.getElem?_set_ne (fun h => hn h.symm), fun _ _ h => h⟩, hrel, _, rfl, rfl⟩
    rw [evaluate_if_val (evaluate_ltLen _ harr hix (by simpa using hv))]
    simp only [decide_eq_true hi, if_true]
    simpa using evaluate_aupdate { s with clock := s.clock } harr hix hx (by simpa using hv) hi
  · have hi' : ¬ i < st.size := by rw [hsz]; exact hi
    have hrel : (arrRel A aloc).rel (st.setIfInBounds i y) s.refs :=
      ⟨vs, hv, by simpa [Array.setIfInBounds, hi'] using hF⟩
    refine ⟨s.refs, .val [.conv none []], ⟨s.clock, s.clock, ?_⟩, Frame.refl _ _, hrel, _, rfl, rfl⟩
    rw [evaluate_if_val (evaluate_ltLen _ harr hix (by simpa using hv))]
    simp only [decide_eq_false hi, Bool.false_eq_true, if_false]
    rw [Flapjack.EvaluateHOL.evaluate]
    simp [doConCheck, buildConv, Flapjack.EvaluateHOL.evaluate]

/-! ## Monadic values: thunks -/

/-- Function application with any non-timeout result. -/
theorem Runs.app_opapp_any {τ : Type} {s s₁ s₂ : State τ} {env env' : SemEnv Value}
    {ef ex body : Exp} {vf vx : Value} {r : Result (List Value) Value}
    (hargs : Runs s env [ex, ef] s₁ (.val [vx, vf]))
    (happ : doOpApp [vf, vx] = some (env', body))
    (hbody : Runs s₁ env' [body] s₂ r) (hr : r ≠ .err (.abort .timeoutError)) :
    Runs s env [.app .opapp [ef, ex]] s₂ r := by
  obtain ⟨a₁, a₂, ha⟩ := hargs
  obtain ⟨b₁, b₂, hb⟩ := hbody
  refine ⟨(b₁ + 1) + a₁, a₂ + b₂, ?_⟩
  have ha' := Runs.add_clock ha (by simp) (b₁ + 1)
  rw [evaluate_app_opapp ha' happ (by simp)]
  have hb' := Runs.add_clock hb hr a₂
  have : decClock { s₁ with clock := b₁ + 1 + a₂ } = { s₁ with clock := a₂ + b₁ } := by
    simp [decClock]; omega
  rw [this]
  exact hb'

/-- A monadic computation as a CakeML value: a function of the state's handle
(the location of the cell holding it: `RF loc` is the state relation at that
location) which, applied to the handle, runs the computation (`EvalM`). The
handle is passed at run time, so closures never capture a fixed location and
the state can be allocated by the code that runs the computation. -/
def MRET {σ ε β : Type} (RF : Nat → StateRel σ) (A : RefInv β) (B : RefInv ε) :
    RefInv (StateT σ (Except ε) β) := fun m v =>
  ∀ (τ : Type) (s : State τ) (st : σ) (b : Bool) (loc : Nat), (RF loc).rel st s.refs →
    ∃ env e, doOpApp [v, .loc b loc] = some (env, e) ∧
    ∃ refs' res, Runs s env [e] { s with refs := refs' } res ∧ Frame (RF loc) s.refs refs' ∧
      MRes (RF loc) A B (m st) refs' res

/-- `fn h => body` is the computation `body` runs, the handle bound to `h`. -/
theorem Eval_MRET_fn {σ ε β : Type} {RF : Nat → StateRel σ} {A : RefInv β} {B : RefInv ε}
    {env : SemEnv Value} {h : VarN} {body : Exp} {m : StateT σ (Except ε) β}
    (hb : ∀ b loc, EvalM (RF loc) { env with v := nsBind h (.loc b loc) env.v } body A B m) :
    Eval env (.fn h body) (MRET RF A B m) := by
  apply Eval_fn
  intro τ s st b loc hst
  exact ⟨_, _, rfl, hb b loc τ s st hst⟩

/-- Applying a computation to the handle runs it. -/
theorem EvalM_run {σ ε β : Type} {RF : Nat → StateRel σ} {A : RefInv β} {B : RefInv ε}
    {env : SemEnv Value} {ef : Exp} {h : Ident ModN VarN} {b : Bool} {loc : Nat}
    {m : StateT σ (Except ε) β} (hh : nsLookup env.v h = some (.loc b loc))
    (hf : Eval env ef (MRET RF A B m)) :
    EvalM (RF loc) env (.app .opapp [ef, .var h]) A B m := by
  intro τ s st hst
  obtain ⟨vf, extra, hfr, hM⟩ := hf τ s
  have hst₁ := StateRel.rel_append hst extra
  obtain ⟨env', body, happ, refs', res, hrun, hfm, hm⟩ := hM τ { s with refs := s.refs ++ extra } st b loc hst₁
  have hargs : Runs s env [.var h, ef] { s with refs := s.refs ++ extra } (.val [.loc b loc, vf]) := by
    have hv : Runs s env [.var h] s (.val [.loc b loc]) := ⟨0, 0, by simp [evaluate, hh]⟩
    obtain ⟨a₁, a₂, ha⟩ := hv
    obtain ⟨c₁, c₂, hc⟩ := hfr.runs
    refine ⟨c₁, c₂, ?_⟩
    have ha' : evaluate { s with clock := c₁ } env [.var h] = ({ s with clock := c₁ }, .val [.loc b loc]) := by
      simp [evaluate, hh]
    exact evaluate_cons_val ha' hc
  refine ⟨refs', res, Runs.app_opapp_any hargs happ (by simpa using hrun) hm.not_timeout,
    (Frame.append hst extra).trans hfm, hm⟩

/-! ## Control -/

/-- `if c then e₂ else e₃`, the condition pure. -/
theorem EvalM_if {σ ε α : Type} {R : StateRel σ} {env : SemEnv Value} {c e₂ e₃ : Exp}
    {A : RefInv α} {B : RefInv ε} {b : Bool} {f g : StateT σ (Except ε) α}
    (hc : Eval env c (BOOL b)) (h₂ : b = true → EvalM R env e₂ A B f)
    (h₃ : b = false → EvalM R env e₃ A B g) :
    EvalM R env (.if_ c e₂ e₃) A B (if b then f else g) := by
  intro τ s st hst
  obtain ⟨cv, extra, hcr, hB⟩ := hc τ s
  have hcv : cv = boolValue b := hB
  subst hcv
  have hst₁ := StateRel.rel_append hst extra
  cases b with
  | true =>
    obtain ⟨refs', res, hr, hfr, hm⟩ := h₂ rfl τ { s with refs := s.refs ++ extra } st hst₁
    exact ⟨refs', res, Runs.if_ hcr.runs (by simpa using hr) hm.not_timeout,
      (Frame.append hst extra).trans hfr, hm⟩
  | false =>
    obtain ⟨refs', res, hr, hfr, hm⟩ := h₃ rfl τ { s with refs := s.refs ++ extra } st hst₁
    exact ⟨refs', res, Runs.if_ hcr.runs (by simpa using hr) hm.not_timeout,
      (Frame.append hst extra).trans hfr, hm⟩

/-! ## `handle` -/

theorem Runs.handle_val {τ : Type} {s s₁ : State τ} {env : SemEnv Value} {e : Exp}
    {cls : List (Pat × Exp)} {v : Value} (h : Runs s env [e] s₁ (.val [v])) :
    Runs s env [.handle e cls] s₁ (.val [v]) := by
  obtain ⟨a₁, a₂, ha⟩ := h
  refine ⟨a₁, a₂, ?_⟩
  have hfix : fixClock { s with clock := a₁ } ({ s₁ with clock := a₂ }, (Result.val [v] : Result (List Value) Value)) =
      ({ s₁ with clock := a₂ }, .val [v]) := by
    rw [← ha]; exact fixClock_evaluate _ env _
  rw [evaluate]
  simp [ha, hfix]

/-- `e handle x => rhs`, `e` raising: `rhs` with `x` bound to the exception. -/
theorem Runs.handle_raise {τ : Type} {s s₁ s₂ : State τ} {env : SemEnv Value} {e rhs : Exp}
    {x : VarN} {v : Value} {r : Result (List Value) Value}
    (h : Runs s env [e] s₁ (.err (.raise v)))
    (h₂ : Runs s₁ { env with v := nsAppend (alistToNs [(x, v)]) env.v } [rhs] s₂ r)
    (hr : r ≠ .err (.abort .timeoutError)) :
    Runs s env [.handle e [(.pvar x, rhs)]] s₂ r := by
  obtain ⟨a₁, a₂, ha⟩ := h
  obtain ⟨b₁, b₂, hb⟩ := h₂
  refine ⟨a₁ + b₁, b₂ + a₂, ?_⟩
  have ha' := evaluate_add_clock ha (by simp) b₁
  have hfix : fixClock { s with clock := a₁ + b₁ } ({ s₁ with clock := a₂ + b₁ },
      (Result.err (.raise v) : Result (List Value) Value)) = ({ s₁ with clock := a₂ + b₁ }, .err (.raise v)) := by
    rw [← ha']; exact fixClock_evaluate _ env _
  rw [evaluate]
  simp only [ha', hfix]
  simp only [canPmatchAll, pmatch, List.map, List.all_cons, List.all_nil, Bool.and_true,
    ite_true, evaluateMatch, patBindings, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_self]
  have hb' := evaluate_add_clock hb hr a₂
  rw [Nat.add_comm a₂ b₁]
  exact hb'

/-! ## Derived state operations, as `bind`, `get`, `set` and `pure` -/

theorem modify_eq_bind {σ ε : Type} (f : σ → σ) :
    (modify f : StateT σ (Except ε) PUnit) = (get >>= fun s => set (f s)) := rfl

theorem modifyGet_eq_bind {σ ε α : Type} (f : σ → α × σ) :
    (modifyGet f : StateT σ (Except ε) α) = (get >>= fun s => set (f s).2 >>= fun _ => pure (f s).1) := rfl

/-! ## Running a computation on a fresh reference -/

/-- Run a state-exception computation from `init`, keeping its result. The
translation runs it on a fresh reference (`Eval_runRef`). -/
def runRef {σ ε α : Type} (init : σ) (m : StateT σ (Except ε) α) : Except ε α :=
  match m init with
  | .ok (a, _) => .ok a
  | .error e => .error e

theorem Runs.opref {τ : Type} {s s₁ : State τ} {env : SemEnv Value} {e : Exp} {v : Value}
    (h : Runs s env [e] s₁ (.val [v])) :
    Runs s env [.app .opref [e]] { s₁ with refs := s₁.refs ++ [.refv v] }
      (.val [.loc true s₁.refs.length]) := by
  obtain ⟨a₁, a₂, ha⟩ := h
  refine ⟨a₁, a₂, ?_⟩
  have := evaluate_app_simple (s := { s with clock := a₁ }) (s₁ := { s₁ with clock := a₂ }) (env := env)
    (op := .opref) (args := [e]) (vs := [v]) (refs := s₁.refs ++ [.refv v]) (ffi := s₁.ffi)
    (r := .val (.loc true s₁.refs.length)) (by simpa using ha) rfl
    (by simp [doApp, doAppBasic, doAppNumericCore, storeAlloc])
  simpa [listResult] using this

/-- Run `m` on a fresh reference holding `init`, as pure code: the result of
`m init`, its value through `eok` (with `x` bound) and its exception through
`eerr` (with `y` bound, by `handle`). -/
theorem Eval_runRef {σ ε α β : Type} {S : RefInv σ} {A : RefInv α} {B : RefInv ε} {P : RefInv β}
    {env : SemEnv Value} {ei em eok eerr : Exp} {h x y : VarN} {init : σ}
    {m : StateT σ (Except ε) α} {ok : α → β} {err : ε → β}
    (hi : Eval env ei (S init))
    (hm : ∀ b loc, Eval { env with v := nsOptBind (some h) (.loc b loc) env.v } em (MRET (refRel S) A B m))
    (hok : ∀ b loc a v, A a v →
      Eval { env with v := nsOptBind (some x) v (nsOptBind (some h) (.loc b loc) env.v) } eok (P (ok a)))
    (herr : ∀ b loc e v, B e v →
      Eval { env with v := nsAppend (alistToNs [(y, v)]) (nsOptBind (some h) (.loc b loc) env.v) } eerr
        (P (err e))) :
    Eval env (.let_ (some h) (.app .opref [ei])
      (.handle (.let_ (some x) (.app .opapp [em, .var (.short h)]) eok) [(.pvar y, eerr)]))
      (P (match m init with | .ok (a, _) => ok a | .error e => err e)) := by
  intro τ s
  obtain ⟨vi, extra, hvi, hS⟩ := hi τ s
  let s₁ : State τ := { s with refs := s.refs ++ extra }
  let loc := s₁.refs.length
  have href := Runs.opref (s := s) (s₁ := s₁) hvi.runs
  let env₁ : SemEnv Value := { env with v := nsOptBind (some h) (.loc true loc) env.v }
  let s₂ : State τ := { s₁ with refs := s₁.refs ++ [.refv vi] }
  have hst : (refRel S loc).rel init s₂.refs := ⟨vi, by simp [s₂, loc], hS⟩
  have hrun := EvalM_run (RF := refRel S) (env := env₁) (h := .short h) (b := true) (loc := loc)
    (by simp [env₁, nsOptBind, nsLookup_nsBind_short]) (hm true loc)
  obtain ⟨refs', res, hr, hfr, hres⟩ := hrun τ s₂ init hst
  -- the cells below the new reference are unchanged: the run only appends to `s.refs`
  have hpre : ∀ l < s₁.refs.length, refs'[l]? = s₂.refs[l]? := fun l hl =>
    hfr.2.1 l (by simp [s₂]; omega) (fun ho => by simp [refRel] at ho; omega)
  have hlen : s₂.refs.length ≤ refs'.length := hfr.1
  have hext : refs' = s.refs ++ refs'.drop s.refs.length := by
    apply List.ext_getElem?
    intro l
    by_cases hl : l < s.refs.length
    · rw [List.getElem?_append_left (by simpa using hl), hpre l (by simp [s₁]; omega)]
      simp [s₂, s₁, List.getElem?_append_left hl]
    · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
      congr 1; omega
  revert hres
  cases hm' : m init with
  | ok p =>
    obtain ⟨a, st'⟩ := p
    intro hres
    obtain ⟨_, v, hv, hA⟩ := hres
    subst hv
    obtain ⟨w, extra₂, hw, hP⟩ := hok true loc a v hA τ { s with refs := refs' }
    refine ⟨w, refs'.drop s.refs.length ++ extra₂, ?_, hP⟩
    apply Runs.evalRel
    have hlet := Runs.let_ (n := some x) (env := env₁) hr (by simpa using hw.runs) (by simp)
    have hh := Runs.handle_val (cls := [(.pvar y, eerr)]) hlet
    have := Runs.let_ (n := some h) (env := env) href (by simpa [s₂, env₁] using hh) (by simp)
    rw [hext] at this
    simpa [List.append_assoc] using this
  | error e =>
    intro hres
    obtain ⟨v, hv, hB⟩ := hres
    subst hv
    obtain ⟨w, extra₂, hw, hP⟩ := herr true loc e v hB τ { s with refs := refs' }
    refine ⟨w, refs'.drop s.refs.length ++ extra₂, ?_, hP⟩
    apply Runs.evalRel
    have hlet := Runs.let_err (n := some x) (e₂ := eok) (env := env₁) hr
    have hh := Runs.handle_raise (x := y) (rhs := eerr) hlet (by simpa [env₁] using hw.runs) (by simp)
    have := Runs.let_ (n := some h) (env := env) href (by simpa [s₂, env₁] using hh) (by simp)
    rw [hext] at this
    simpa [List.append_assoc] using this

end ConPastel.Translator
