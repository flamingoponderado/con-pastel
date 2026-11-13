import ConPastel.Main.Code
import ConPastel.Spec
import Batteries.Tactic.OpenPrivate
import ConPastel.Translator.List

/-!
# `readAll` reads the whole input

Run in the closure environment `E` (where `buf` is the byte array at store
location `ℓ`), the body of `readAll` with accumulator `acc` consumes the
remaining input `inp` one byte per `read` call, and returns the list of the
input's byte values reversed onto `acc`. It only adds `read` events, so
the written bytes are unchanged.
-/

namespace ConPastel.Main
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString ConPastel.Translator

def readAllFuns : List (VarN × VarN × Exp) := [(ofString readAllName, ofString "acc", readAllBody)]

def readAllClosure (E : SemEnv Value) : Value := .recclosure E readAllFuns (ofString readAllName)

/-- An io-event of the `read` call. -/
def IsRead (e : HolIoEvent) : Prop := e.name = .extCall (ofString "read")

theorem writtenBytes_append_reads (evs rs : List HolIoEvent) (h : ∀ e ∈ rs, IsRead e) :
    writtenBytes (evs ++ rs) = writtenBytes evs := by
  induction rs generalizing evs with
  | nil => simp
  | cons r rs ih =>
    rw [← List.singleton_append, ← List.append_assoc, ih _ (fun e he => h e (.tail _ he))]
    have : r.name ≠ .extCall (ofString "write") := by
      rw [h r (.head _)]; decide
    simp [writtenBytes, this]

/-- The values of a list of bytes. -/
def byteNats (bs : List (BitVec 8)) : List Nat := bs.map BitVec.toNat

/-- The `read` FFI call on the buffer, at the end of the input. -/
theorem eval_read_eof (env : SemEnv Value) (ℓ : Nat)
    (hbuf : nsLookup env.v (.short (ofString bufName)) = some (.loc true ℓ))
    (s : State Stdio) (b0 b1 : BitVec 8) (hst : s.refs[ℓ]? = some (.w8array [b0, b1]))
    (hor : s.ffi.oracle = stdioOracle) (hin : s.ffi.ffiState.input = []) :
    evaluate s env [.app (.ffi (ofString "read")) [.lit (.strLit (ofString "")), var bufName]] =
      ({ s with
          refs := s.refs.set ℓ (.w8array [0, b1])
          ffi := { s.ffi with
            ioEvents := s.ffi.ioEvents ++
              [{ name := .extCall (ofString "read"), configuration := [], bytes := [(b0, 0), (b1, b1)] }] } },
        .val [.conv none []]) := by
  obtain ⟨ck, refs, ⟨o, st, evs⟩, nts, nes, evst⟩ := s
  simp only at hor hin hst
  subst hor
  simp +decide [evaluate, fixClock, getOpClass, headValue, Flapjack.holHd, doApp, doAppNumericCore,
    doAppBasic, storeLookup, storeAssign, callFFIHOL, var, hbuf, hst, hin, stdioOracle,
    storeValueSameType, listResult]

/-- The `read` FFI call on the buffer, with input remaining. -/
theorem eval_read_byte (env : SemEnv Value) (ℓ : Nat)
    (hbuf : nsLookup env.v (.short (ofString bufName)) = some (.loc true ℓ))
    (s : State Stdio) (b0 b1 b : BitVec 8) (rest : List (BitVec 8))
    (hst : s.refs[ℓ]? = some (.w8array [b0, b1]))
    (hor : s.ffi.oracle = stdioOracle) (hin : s.ffi.ffiState.input = b :: rest) :
    evaluate s env [.app (.ffi (ofString "read")) [.lit (.strLit (ofString "")), var bufName]] =
      ({ s with
          refs := s.refs.set ℓ (.w8array [1, b])
          ffi := { s.ffi with
            ffiState := { input := rest }
            ioEvents := s.ffi.ioEvents ++
              [{ name := .extCall (ofString "read"), configuration := [], bytes := [(b0, 1), (b1, b)] }] } },
        .val [.conv none []]) := by
  obtain ⟨ck, refs, ⟨o, st, evs⟩, nts, nes, evst⟩ := s
  simp only at hor hin hst
  subst hor
  simp +decide [evaluate, fixClock, getOpClass, headValue, Flapjack.holHd, doApp, doAppNumericCore,
    doAppBasic, storeLookup, storeAssign, callFFIHOL, var, hbuf, hst, hin, stdioOracle,
    storeValueSameType, listResult]

/-- The loop condition `buf[0] = 0w`. -/
theorem eval_test0 (env : SemEnv Value) (ℓ : Nat)
    (hbuf : nsLookup env.v (.short (ofString bufName)) = some (.loc true ℓ))
    (s : State Stdio) (c d : BitVec 8) (hst : s.refs[ℓ]? = some (.w8array [c, d])) :
    evaluate s env [.app .equality [.app .aw8sub [var bufName, .lit (.intLit 0)], .lit (.word8 0)]] =
      (s, .val [boolValue (decide (c = 0))]) := by
  simp +decide [evaluate, fixClock, getOpClass, headValue, Flapjack.holHd, doApp, doAppNumericCore,
    doAppBasic, storeLookup, var, hbuf, hst, readIndexed, doEq, litSameType, listResult]

/-- The byte value `w2n buf[1]`. -/
theorem eval_byte1 (env : SemEnv Value) (ℓ : Nat)
    (hbuf : nsLookup env.v (.short (ofString bufName)) = some (.loc true ℓ))
    (s : State Stdio) (c d : BitVec 8) (hst : s.refs[ℓ]? = some (.w8array [c, d])) :
    evaluate s env [.app (.fromTo (.wordT .w8) .intT) [.app .aw8sub [var bufName, .lit (.intLit 1)]]] =
      (s, .val [.litv (.intLit d.toNat)]) := by
  simp +decide [evaluate, fixClock, getOpClass, headValue, Flapjack.holHd, doApp, doAppNumericCore,
    doAppBasic, storeLookup, var, hbuf, hst, readIndexed, listResult, checkType, doConversion, theLitvWord8]

theorem lookup_buf_body (E : SemEnv Value) (ℓ : Nat) (accv : Value)
    (hbuf : nsLookup E.v (.short (ofString bufName)) = some (.loc true ℓ)) :
    nsLookup (recBodyEnv E readAllFuns (ofString "acc") accv).v (.short (ofString bufName)) =
      some (.loc true ℓ) := by
  have h1 : ofString bufName ≠ ofString "acc" := by decide
  have h2 : ofString bufName ≠ ofString readAllName := by decide
  simp [recBodyEnv, readAllFuns, buildRecEnv, nsLookup_nsBind_short, h1, h2, hbuf]

theorem lookup_acc_body (E : SemEnv Value) (accv : Value) :
    nsLookup (recBodyEnv E readAllFuns (ofString "acc") accv).v (.short (ofString "acc")) = some accv := by
  simp [recBodyEnv, nsLookup_nsBind_short]

theorem lookup_readAll_body (E : SemEnv Value) (accv : Value) :
    nsLookup (recBodyEnv E readAllFuns (ofString "acc") accv).v (.short (ofString readAllName)) =
      some (readAllClosure E) := by
  have h1 : ofString readAllName ≠ ofString "acc" := by decide
  simp [recBodyEnv, readAllFuns, buildRecEnv, nsLookup_nsBind_short, h1, readAllClosure]

theorem readAll_spec (E : SemEnv Value) (ℓ : Nat)
    (hbuf : nsLookup E.v (.short (ofString bufName)) = some (.loc true ℓ))
    (hcons : HasListCons E.c) :
    ∀ (inp : List (BitVec 8)) (acc : List Nat) (accv : Value), LIST NAT acc accv →
    ∀ (s : State Stdio) (c d : BitVec 8), s.refs[ℓ]? = some (.w8array [c, d]) →
      s.ffi.oracle = stdioOracle → s.ffi.ffiState.input = inp → ∀ extra,
    ∃ refs' reads v,
      evaluate { s with clock := inp.length + extra } (recBodyEnv E readAllFuns (ofString "acc") accv)
          [readAllBody] =
        ({ s with
            clock := extra
            refs := refs'
            ffi := { s.ffi with ffiState := { input := [] }, ioEvents := s.ffi.ioEvents ++ reads } },
          .val [v]) ∧
      LIST NAT ((byteNats inp).reverse ++ acc) v ∧ (∀ e ∈ reads, IsRead e) ∧
      (∃ c' d', refs'[ℓ]? = some (.w8array [c', d'])) := by
  intro inp
  induction inp with
  | nil =>
    intro acc accv hacc s c d hst hor hin extra
    have hb := lookup_buf_body E ℓ accv hbuf
    have hlt : ℓ < s.refs.length := by
      rcases Nat.lt_or_ge ℓ s.refs.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hst
    have hR := eval_read_eof _ ℓ hb { s with clock := extra } c d hst hor hin
    refine ⟨s.refs.set ℓ (.w8array [0, d]),
      [{ name := .extCall (ofString "read"), configuration := [], bytes := [(c, 0), (d, d)] }],
      accv, ?_, by simpa [byteNats] using hacc, ?_, ⟨0, d, List.getElem?_set_self hlt⟩⟩
    · simp only [List.length_nil, Nat.zero_add, readAllBody]
      rw [evaluate_let_val hR]
      have henv : ({ (recBodyEnv E readAllFuns (ofString "acc") accv) with
          v := nsOptBind none (Value.conv none []) (recBodyEnv E readAllFuns (ofString "acc") accv).v } :
            SemEnv Value) = recBodyEnv E readAllFuns (ofString "acc") accv := rfl
      rw [henv]
      rw [evaluate_if_val (eval_test0 _ ℓ hb _ 0 d (List.getElem?_set_self hlt))]
      have hfs : s.ffi.ffiState = { input := [] } := by
        cases h : s.ffi.ffiState; simp_all
      simp [var, evaluate, lookup_acc_body, hfs]
    · intro e he
      simp only [List.mem_singleton] at he
      subst he
      rfl
  | cons b rest ih =>
    intro acc accv hacc s c d hst hor hin extra
    have hb := lookup_buf_body E ℓ accv hbuf
    have hlt : ℓ < s.refs.length := by
      rcases Nat.lt_or_ge ℓ s.refs.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hst
    let env := recBodyEnv E readAllFuns (ofString "acc") accv
    have hR := eval_read_byte env ℓ hb { s with clock := rest.length + 1 + extra } c d b rest hst hor hin
    -- the state after the read
    let s₁ : State Stdio := { s with
      clock := rest.length + 1 + extra
      refs := s.refs.set ℓ (.w8array [1, b])
      ffi := { s.ffi with
        ffiState := { input := rest }
        ioEvents := s.ffi.ioEvents ++
          [{ name := .extCall (ofString "read"), configuration := [], bytes := [(c, 1), (d, b)] }] } }
    have hst₁ : s₁.refs[ℓ]? = some (.w8array [1, b]) := List.getElem?_set_self hlt
    -- the new accumulator
    let vx : Value := .conv (some (.typeStamp consC 1)) [.litv (.intLit b.toNat), accv]
    have hvx : LIST NAT (b.toNat :: acc) vx := ⟨_, _, rfl, hacc, rfl⟩
    have hcon : evaluate s₁ env [.con (some (.short (ofString "::")))
        [.app (.fromTo (.wordT .w8) .intT) [.app .aw8sub [var bufName, .lit (.intLit 1)]], var "acc"]] =
        (s₁, .val [vx]) := by
      have hargs : evaluate s₁ env [var "acc",
          .app (.fromTo (.wordT .w8) .intT) [.app .aw8sub [var bufName, .lit (.intLit 1)]]] =
          (s₁, .val [accv, .litv (.intLit b.toNat)]) :=
        evaluate_cons_val (by simp [var, evaluate, env, lookup_acc_body]) (eval_byte1 env ℓ hb s₁ 1 b hst₁)
      rw [evaluate]
      have hlk : nsLookup env.c (.short (ofString "::")) = some (2, .typeStamp consC 1) := hcons.cons
      simp [doConCheck, hlk, hargs, buildConv, vx, consC]
    have hall : evaluate s₁ env [.con (some (.short (ofString "::")))
        [.app (.fromTo (.wordT .w8) .intT) [.app .aw8sub [var bufName, .lit (.intLit 1)]], var "acc"],
        var readAllName] = (s₁, .val [vx, readAllClosure E]) :=
      evaluate_cons_val hcon (by simp [var, evaluate, env, lookup_readAll_body])
    have happ : doOpApp [readAllClosure E, vx] =
        some (recBodyEnv E readAllFuns (ofString "acc") vx, readAllBody) := by
      simp [doOpApp, readAllClosure, readAllFuns, findRecFun, recBodyEnv]
    have hdec : decClock s₁ = { s₁ with clock := rest.length + extra } := by
      simp only [decClock, s₁]; congr 1; omega
    obtain ⟨refs', reads', v, heval, hlist, hreads, hbuf'⟩ :=
      ih (b.toNat :: acc) vx hvx { s₁ with clock := 0 } 1 b hst₁ hor rfl extra
    refine ⟨refs', { name := .extCall (ofString "read"), configuration := [], bytes := [(c, 1), (d, b)] } :: reads',
      v, ?_, ?_, ?_, hbuf'⟩
    · simp only [List.length_cons, readAllBody]
      rw [evaluate_let_val hR]
      have henv : ({ env with v := nsOptBind none (Value.conv none []) env.v } : SemEnv Value) = env := rfl
      rw [henv]
      rw [evaluate_if_val (eval_test0 env ℓ hb _ 1 b hst₁)]
      have h10 : decide ((1 : BitVec 8) = 0) = false := by decide
      rw [h10]
      simp only [Bool.false_eq_true, ite_false]
      rw [evaluate_app_opapp hall happ (by simp [s₁]), hdec]
      have : ({ s₁ with clock := rest.length + extra } : State Stdio) =
          { ({ s₁ with clock := 0 } : State Stdio) with clock := rest.length + extra } := rfl
      rw [this, heval]
      simp [s₁, List.append_assoc]
    · simpa [byteNats, List.append_assoc] using hlist
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rfl
      · exact hreads e he

end ConPastel.Main
