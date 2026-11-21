import ConPastel.Main.Proof
import ConPastel.Translator.EvalM
import ConPastel.Par.Code
import ConPastel.Par.Spec

/-!
# FFI calls and the stream loop, for any oracle

`eval_ffi_ret`/`eval_ffi_final`: an FFI call `#(name) conf buf` whose oracle answers `.ret` or
`.final`, in any state type. `loop_spec`: the loop `loopBody ffi fname` (the shape of `readAll`)
over any oracle that answers `ffi` with `read`'s protocol over a stream of bytes, returns the stream
reversed onto its accumulator, adding only `ffi` events.
-/

namespace ConPastel.Par
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString ConPastel.Translator ConPastel.Main

/-- The io-event of an FFI call that returned. -/
def ffiEvent (name : String) (conf : List (BitVec 8)) (bytes out : List (BitVec 8)) : HolIoEvent :=
  { name := .extCall (ofString name), configuration := conf, bytes := bytes.zip out }

/-- An FFI call whose oracle returns. -/
theorem eval_ffi_ret {σ : Type} (env : SemEnv Value) (s : State σ) (name bufN : String) (ce : Exp)
    (conf : MlString) (ℓ : Nat) (bytes out : List (BitVec 8)) (st' : σ)
    (hce : evaluate s env [ce] = (s, .val [.litv (.strLit conf)]))
    (hbuf : nsLookup env.v (.short (ofString bufN)) = some (.loc true ℓ))
    (hst : s.refs[ℓ]? = some (.w8array bytes))
    (hne : ofString name ≠ MlString.implode [])
    (ho : s.ffi.oracle (.extCall (ofString name)) s.ffi.ffiState conf.explode bytes = .ret st' out)
    (hlen : out.length = bytes.length) :
    evaluate s env [.app (.ffi (ofString name)) [ce, var bufN]] =
      ({ s with
          refs := s.refs.set ℓ (.w8array out)
          ffi := { s.ffi with
            ffiState := st'
            ioEvents := s.ffi.ioEvents ++ [ffiEvent name conf.explode bytes out] } },
        .val [.conv none []]) := by
  have hargs := evaluate_cons_val (by simp [var, evaluate, hbuf] :
    evaluate s env [var bufN] = (s, .val [.loc true ℓ])) hce
  have hne' : (HolFfiName.extCall (ofString name)) ≠ .extCall (MlString.implode []) := by
    intro h; exact hne (HolFfiName.extCall.inj h)
  have hdo : doApp (s.refs, s.ffi) (.ffi (ofString name)) [.litv (.strLit conf), .loc true ℓ] =
      some ((s.refs.set ℓ (.w8array out),
        { s.ffi with ffiState := st', ioEvents := s.ffi.ioEvents ++ [ffiEvent name conf.explode bytes out] }),
        .val (.conv none [])) := by
    simp [doApp, doAppNumericCore, doAppBasic, storeLookup, storeAssign, callFFIHOL, hst, hne', ho,
      hlen, storeValueSameType, ffiEvent]
  have := evaluate_app_simple (op := .ffi (ofString name)) (args := [ce, var bufN])
    (by simpa using hargs) rfl (by simpa using hdo)
  simpa [listResult] using this

/-- The final event of an FFI call that ends the run. -/
def finalEvent (name : String) (conf bytes : List (BitVec 8)) (oc : HolFfiOutcome) : HolFinalEvent :=
  { name := .extCall (ofString name), configuration := conf, bytes := bytes, outcome := oc }

/-- An FFI call whose oracle ends the run. -/
theorem eval_ffi_final {σ : Type} (env : SemEnv Value) (s : State σ) (name bufN : String) (ce : Exp)
    (conf : MlString) (ℓ : Nat) (bytes : List (BitVec 8)) (oc : HolFfiOutcome)
    (hce : evaluate s env [ce] = (s, .val [.litv (.strLit conf)]))
    (hbuf : nsLookup env.v (.short (ofString bufN)) = some (.loc true ℓ))
    (hst : s.refs[ℓ]? = some (.w8array bytes))
    (hne : ofString name ≠ MlString.implode [])
    (ho : s.ffi.oracle (.extCall (ofString name)) s.ffi.ffiState conf.explode bytes = .final oc) :
    evaluate s env [.app (.ffi (ofString name)) [ce, var bufN]] =
      (s, .err (.abort (.ffiError (finalEvent name conf.explode bytes oc)))) := by
  have hargs := evaluate_cons_val (by simp [var, evaluate, hbuf] :
    evaluate s env [var bufN] = (s, .val [.loc true ℓ])) hce
  have hne' : (HolFfiName.extCall (ofString name)) ≠ .extCall (MlString.implode []) := by
    intro h; exact hne (HolFfiName.extCall.inj h)
  have hdo : doApp (s.refs, s.ffi) (.ffi (ofString name)) [.litv (.strLit conf), .loc true ℓ] =
      some ((s.refs, s.ffi), .err (.abort (.ffiError (finalEvent name conf.explode bytes oc)))) := by
    simp [doApp, doAppNumericCore, doAppBasic, storeLookup, callFFIHOL, hst, hne', ho, finalEvent]
  have := evaluate_app_simple (op := .ffi (ofString name)) (args := [ce, var bufN])
    (by simpa using hargs) rfl (by simpa using hdo)
  simpa [listResult] using this

theorem eval_strLit {σ : Type} (s : State σ) (env : SemEnv Value) (str : String) :
    evaluate s env [.lit (.strLit (ofString str))] = (s, .val [.litv (.strLit (ofString str))]) := by
  simp [evaluate]

/-! ## The stream loop -/

/-- The oracle answers `ffi` with `read`'s protocol over the stream `get`. -/
structure StreamFfi {σ : Type} (o : HolOracle σ) (ffi : String) (get : σ → List (BitVec 8))
    (set : σ → List (BitVec 8) → σ) : Prop where
  ans : ∀ st conf (bytes : List (BitVec 8)), bytes.length = 2 →
    o (.extCall (ofString ffi)) st conf bytes =
      .ret (set st (streamAnswer (get st) bytes).1) (streamAnswer (get st) bytes).2
  get_set : ∀ st r, get (set st r) = r
  set_set : ∀ st a b, set (set st a) b = set st b
  ne : ofString ffi ≠ MlString.implode []

def loopFuns (ffi fname : String) : List (VarN × VarN × Exp) :=
  [(ofString fname, ofString "acc", loopBody ffi fname)]

def loopClosure (E : SemEnv Value) (ffi fname : String) : Value :=
  .recclosure E (loopFuns ffi fname) (ofString fname)

/-- An io-event of the call `ffi`. -/
def IsCall (ffi : String) (e : HolIoEvent) : Prop := e.name = .extCall (ofString ffi)

theorem eval_test0' {σ : Type} (env : SemEnv Value) (bufN : String) (ℓ : Nat)
    (hbuf : nsLookup env.v (.short (ofString bufN)) = some (.loc true ℓ))
    (s : State σ) (bs : List (BitVec 8)) (c : BitVec 8) (hst : s.refs[ℓ]? = some (.w8array (c :: bs))) :
    evaluate s env [.app .equality [.app .aw8sub [var bufN, .lit (.intLit 0)], .lit (.word8 0)]] =
      (s, .val [boolValue (decide (c = 0))]) := by
  simp +decide [evaluate, fixClock, getOpClass, headValue, Flapjack.holHd, doApp, doAppNumericCore,
    doAppBasic, storeLookup, var, hbuf, hst, readIndexed, doEq, litSameType, listResult]

/-- `w2n b[i]`. -/
theorem eval_byte {σ : Type} (env : SemEnv Value) (bufN : String) (ℓ : Nat)
    (hbuf : nsLookup env.v (.short (ofString bufN)) = some (.loc true ℓ))
    (s : State σ) (bs : List (BitVec 8)) (i : Nat) (hi : i < bs.length)
    (hst : s.refs[ℓ]? = some (.w8array bs)) :
    evaluate s env [.app (.fromTo (.wordT .w8) .intT) [.app .aw8sub [var bufN, .lit (.intLit i)]]] =
      (s, .val [.litv (.intLit bs[i].toNat)]) := by
  have hi' : ¬ ((i : Int) < 0) := by omega
  have hi'' : (i : Int).toNat < bs.length := by simpa using hi
  simp +decide [evaluate, fixClock, getOpClass, headValue, Flapjack.holHd, doApp, doAppNumericCore,
    doAppBasic, storeLookup, var, hbuf, hst, readIndexed, listResult, checkType, doConversion,
    theLitvWord8, hi, hi', hi'']

theorem loop_lookup_buf (E : SemEnv Value) (ffi fname bufN : String) (ℓ : Nat) (accv : Value)
    (hbuf : nsLookup E.v (.short (ofString bufN)) = some (.loc true ℓ))
    (h1 : ofString bufN ≠ ofString "acc") (h2 : ofString bufN ≠ ofString fname) :
    nsLookup (recBodyEnv E (loopFuns ffi fname) (ofString "acc") accv).v (.short (ofString bufN)) =
      some (.loc true ℓ) := by
  simp [recBodyEnv, loopFuns, buildRecEnv, nsLookup_nsBind_short, h1, h2, hbuf]

theorem loop_lookup_acc (E : SemEnv Value) (ffi fname : String) (accv : Value) :
    nsLookup (recBodyEnv E (loopFuns ffi fname) (ofString "acc") accv).v (.short (ofString "acc")) =
      some accv := by
  simp [recBodyEnv, nsLookup_nsBind_short]

theorem loop_lookup_self (E : SemEnv Value) (ffi fname : String) (accv : Value)
    (h1 : ofString fname ≠ ofString "acc") :
    nsLookup (recBodyEnv E (loopFuns ffi fname) (ofString "acc") accv).v (.short (ofString fname)) =
      some (loopClosure E ffi fname) := by
  simp [recBodyEnv, loopFuns, buildRecEnv, nsLookup_nsBind_short, h1, loopClosure]

/-- **The stream loop** returns the stream reversed onto its accumulator. -/
theorem loop_spec {σ : Type} {o : HolOracle σ} {ffi fname : String} {get : σ → List (BitVec 8)}
    {set : σ → List (BitVec 8) → σ} (hO : StreamFfi o ffi get set)
    (E : SemEnv Value) (ℓ : Nat)
    (hbuf : nsLookup E.v (.short (ofString bufName)) = some (.loc true ℓ))
    (hcons : HasListCons E.c)
    (h1 : ofString bufName ≠ ofString "acc") (h2 : ofString bufName ≠ ofString fname)
    (h3 : ofString fname ≠ ofString "acc") :
    ∀ (inp : List (BitVec 8)) (acc : List Nat) (accv : Value), LIST NAT acc accv →
    ∀ (s : State σ) (c d : BitVec 8), s.refs[ℓ]? = some (.w8array [c, d]) →
      s.ffi.oracle = o → get s.ffi.ffiState = inp → ∀ extra,
    ∃ refs' calls v,
      evaluate { s with clock := inp.length + extra }
          (recBodyEnv E (loopFuns ffi fname) (ofString "acc") accv) [loopBody ffi fname] =
        ({ s with
            clock := extra
            refs := refs'
            ffi := { s.ffi with ffiState := set s.ffi.ffiState [], ioEvents := s.ffi.ioEvents ++ calls } },
          .val [v]) ∧
      LIST NAT ((byteNats inp).reverse ++ acc) v ∧ (∀ e ∈ calls, IsCall ffi e) ∧
      (∃ c' d', refs'[ℓ]? = some (.w8array [c', d'])) := by
  intro inp
  induction inp with
  | nil =>
    intro acc accv hacc s c d hst hor hin extra
    have hb := loop_lookup_buf E ffi fname bufName ℓ accv hbuf h1 h2
    have hlt : ℓ < s.refs.length := by
      rcases Nat.lt_or_ge ℓ s.refs.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hst
    have ho : ({ s with clock := extra } : State σ).ffi.oracle (.extCall (ofString ffi))
        s.ffi.ffiState (ofString "").explode [c, d] = .ret (set s.ffi.ffiState []) [0, d] := by
      simp only [hor]; rw [hO.ans _ _ _ rfl, hin]; rfl
    have hR := eval_ffi_ret _ { s with clock := extra } ffi bufName _ _ ℓ [c, d] [0, d] _
      (eval_strLit _ _ "") hb hst hO.ne ho rfl
    refine ⟨s.refs.set ℓ (.w8array [0, d]), [ffiEvent ffi (ofString "").explode [c, d] [0, d]],
      accv, ?_, by simpa [byteNats] using hacc, ?_, ⟨0, d, List.getElem?_set_self hlt⟩⟩
    · simp only [List.length_nil, Nat.zero_add, loopBody]
      rw [evaluate_let_val hR]
      have henv : ({ (recBodyEnv E (loopFuns ffi fname) (ofString "acc") accv) with
          v := nsOptBind none (Value.conv none []) (recBodyEnv E (loopFuns ffi fname) (ofString "acc") accv).v } :
            SemEnv Value) = recBodyEnv E (loopFuns ffi fname) (ofString "acc") accv := rfl
      rw [henv]
      rw [evaluate_if_val (eval_test0' _ bufName ℓ hb _ [d] 0 (List.getElem?_set_self hlt))]
      simp [var, evaluate, loop_lookup_acc]
    · intro e he
      simp only [List.mem_singleton] at he
      subst he
      rfl
  | cons b rest ih =>
    intro acc accv hacc s c d hst hor hin extra
    have hb := loop_lookup_buf E ffi fname bufName ℓ accv hbuf h1 h2
    have hlt : ℓ < s.refs.length := by
      rcases Nat.lt_or_ge ℓ s.refs.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hst
    let env := recBodyEnv E (loopFuns ffi fname) (ofString "acc") accv
    have ho : ({ s with clock := rest.length + 1 + extra } : State σ).ffi.oracle (.extCall (ofString ffi))
        s.ffi.ffiState (ofString "").explode [c, d] = .ret (set s.ffi.ffiState rest) [1, b] := by
      simp only [hor]; rw [hO.ans _ _ _ rfl, hin]; rfl
    have hR := eval_ffi_ret env { s with clock := rest.length + 1 + extra } ffi bufName _ _ ℓ
      [c, d] [1, b] _ (eval_strLit _ _ "") hb hst hO.ne ho rfl
    let ev := ffiEvent ffi (ofString "").explode [c, d] [1, b]
    let s₁ : State σ := { s with
      clock := rest.length + 1 + extra
      refs := s.refs.set ℓ (.w8array [1, b])
      ffi := { s.ffi with ffiState := set s.ffi.ffiState rest, ioEvents := s.ffi.ioEvents ++ [ev] } }
    have hst₁ : s₁.refs[ℓ]? = some (.w8array [1, b]) := List.getElem?_set_self hlt
    let vx : Value := .conv (some (.typeStamp consC 1)) [.litv (.intLit b.toNat), accv]
    have hvx : LIST NAT (b.toNat :: acc) vx := ⟨_, _, rfl, hacc, rfl⟩
    have hcon : evaluate s₁ env [.con (some (.short (ofString "::")))
        [.app (.fromTo (.wordT .w8) .intT) [.app .aw8sub [var bufName, .lit (.intLit 1)]], var "acc"]] =
        (s₁, .val [vx]) := by
      have hargs : evaluate s₁ env [var "acc",
          .app (.fromTo (.wordT .w8) .intT) [.app .aw8sub [var bufName, .lit (.intLit 1)]]] =
          (s₁, .val [accv, .litv (.intLit b.toNat)]) :=
        evaluate_cons_val (by simp [var, evaluate, env, loop_lookup_acc])
          (eval_byte env bufName ℓ hb s₁ [1, b] 1 (by simp) hst₁)
      rw [evaluate]
      have hlk : nsLookup env.c (.short (ofString "::")) = some (2, .typeStamp consC 1) := hcons.cons
      simp [doConCheck, hlk, hargs, buildConv, vx, consC]
    have hall : evaluate s₁ env [.con (some (.short (ofString "::")))
        [.app (.fromTo (.wordT .w8) .intT) [.app .aw8sub [var bufName, .lit (.intLit 1)]], var "acc"],
        var fname] = (s₁, .val [vx, loopClosure E ffi fname]) :=
      evaluate_cons_val hcon (by simp [var, evaluate, env, loop_lookup_self _ _ _ _ h3])
    have happ : doOpApp [loopClosure E ffi fname, vx] =
        some (recBodyEnv E (loopFuns ffi fname) (ofString "acc") vx, loopBody ffi fname) := by
      simp [doOpApp, loopClosure, loopFuns, findRecFun, recBodyEnv]
    have hdec : decClock s₁ = { s₁ with clock := rest.length + extra } := by
      simp only [decClock, s₁]; congr 1; omega
    obtain ⟨refs', calls', v, heval, hlist, hcalls, hbuf'⟩ :=
      ih (b.toNat :: acc) vx hvx { s₁ with clock := 0 } 1 b hst₁ hor (hO.get_set _ _) extra
    refine ⟨refs', ev :: calls', v, ?_, ?_, ?_, hbuf'⟩
    · simp only [List.length_cons, loopBody]
      rw [evaluate_let_val hR]
      have henv : ({ env with v := nsOptBind none (Value.conv none []) env.v } : SemEnv Value) = env := rfl
      rw [henv]
      rw [evaluate_if_val (eval_test0' env bufName ℓ hb _ [b] 1 hst₁)]
      have h10 : decide ((1 : BitVec 8) = 0) = false := by decide
      rw [h10]
      simp only [Bool.false_eq_true, ite_false]
      rw [evaluate_app_opapp hall happ (by simp [s₁]), hdec]
      have : ({ s₁ with clock := rest.length + extra } : State σ) =
          { ({ s₁ with clock := 0 } : State σ) with clock := rest.length + extra } := rfl
      rw [this, heval]
      simp [s₁, List.append_assoc, hO.set_set]
    · simpa [byteNats, List.append_assoc] using hlist
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rfl
      · exact hcalls e he

end ConPastel.Par
