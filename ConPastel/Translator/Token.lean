import ConPastel.Translator.EvalM

/-!
# Identity tokens

CakeML has no pointer test, but it has references, and its `=` compares two
references by location. A datatype registered with `cake_token` stores, in
every constructor, a fresh reference allocated when the value is built
(`tokExp`, `ref ()`): its *identity token*. The invariant only says the token
is a reference (`TOKEN`), so the token carries no meaning — but two values
built separately have different tokens, and CakeML's `=` on two values
compares the tokens before the children.

So on such a type `=` is a *pointer test*: it returns at once (the stored
words, then the tokens, differ — or the two are the same object), and `true`
means equal values. It is no longer a decision of equality: equal values
built separately compare unequal.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL

/-- An identity token: some reference. -/
def TOKEN (v : Value) : Prop := ∃ n, v = .loc true n

/-- `ref ()`: a fresh identity token. -/
def tokExp : Exp := .app .opref [.con none []]

theorem Eval_tok (env : SemEnv Value) : Eval env tokExp TOKEN := by
  intro σ s
  have hu : Runs s env [.con none []] s (.val [.conv none []]) := ⟨0, 0, by simp [evaluate, doConCheck, buildConv]⟩
  have := Runs.opref hu
  exact ⟨_, [.refv (.conv none [])], this.evalRel, _, rfl⟩

/-! ## Sound equality, and the pointer test -/

/-- The outcome of CakeML's `=` on two values: `false`, or `true` and `P`. -/
def EqOut (r : EqResult) (P : Prop) : Prop := r = .val false ∨ (r = .val true ∧ P)

/-- CakeML's `=` on representations never fails, and `true` means equal values. -/
def EqSound {α : Type} (A : RefInv α) : Prop :=
  ∀ x y v w, A x v → A y w → EqOut (doEq v w) (x = y)

theorem eqOut_token {v w : Value} (hv : TOKEN v) (hw : TOKEN w) : EqOut (doEq v w) True := by
  obtain ⟨n, rfl⟩ := hv; obtain ⟨m, rfl⟩ := hw
  by_cases h : n = m
  · exact .inr ⟨by simp [doEq, h], trivial⟩
  · exact .inl (by simp [doEq, h])

theorem eqOut_nil {P : Prop} (h : P) : EqOut (doEqList [] []) P := .inr ⟨by simp [doEqList], h⟩

theorem eqOut_cons {x y : Value} {xs ys : List Value} {P Q : Prop}
    (h : EqOut (doEq x y) P) (k : P → EqOut (doEqList xs ys) Q) :
    EqOut (doEqList (x :: xs) (y :: ys)) Q := by
  rcases h with h | ⟨h, hp⟩
  · exact .inl (by simp [doEqList, h])
  · have := k hp
    simp only [doEqList, h]
    exact this

theorem eqOut_false {r : EqResult} {P : Prop} (h : r = .val false) : EqOut r P := .inl h

/-- CakeML's `=` as a pointer test: `true` means equal values. -/
theorem Eval_eqSound {α : Type} {A : RefInv α} (hA : EqSound A) {env : SemEnv Value} {e₁ e₂ : Exp}
    {a b : α} (h₁ : Eval env e₁ (A a)) (h₂ : Eval env e₂ (A b)) :
    Eval env (.app .equality [e₁, e₂]) (fun v => ∃ r, BOOL r v ∧ (r = true → a = b)) :=
  Eval_binop rfl h₁ h₂ fun v₁ v₂ p₁ p₂ => by
    rcases hA _ _ _ _ p₁ p₂ with he | ⟨he, hab⟩
    · exact ⟨_, ⟨false, rfl, by simp⟩, fun refs ffi => by simp [doApp, doAppBasic, doAppNumericCore, he]⟩
    · exact ⟨_, ⟨true, rfl, fun _ => hab⟩, fun refs ffi => by simp [doApp, doAppBasic, doAppNumericCore, he]⟩

/-- `if` on a condition known only up to a property `R` of its value. -/
theorem Eval_ifP {env : SemEnv Value} {c e₂ e₃ : Exp} {R : Bool → Prop} {P : Value → Prop}
    (hc : Eval env c (fun v => ∃ b, BOOL b v ∧ R b)) (h₂ : ∀ b, R b → b = true → Eval env e₂ P)
    (h₃ : ∀ b, R b → b = false → Eval env e₃ P) :
    Eval env (.if_ c e₂ e₃) P := by
  intro σ s
  obtain ⟨v, r₁, hv, b, pv, hr⟩ := hc σ s
  cases pv
  have hbr : Eval env (if b then e₂ else e₃) P := by
    cases b
    · exact h₃ false hr rfl
    · exact h₂ true hr rfl
  obtain ⟨w, r₂, hw, qw⟩ := hbr σ { s with refs := s.refs ++ r₁ }
  refine ⟨w, r₁ ++ r₂, ?_, qw⟩
  apply Runs.evalRel
  have := Runs.if_ hv.runs hw.runs (by simp)
  simpa [List.append_assoc] using this

/-! ## The pointer test as a choice

`ptrSel a b t e h` is `e`, whose value `t p` also is when `a = b` (`h`): the
translation tests `a` and `b` with CakeML's `=` (`Eval_ptrSel`), a pointer test
on a type with identity tokens, and takes `t` when it succeeds. -/

/-- `e`, or equally `t p` when `a = b`. -/
def ptrSel {α β : Type} (a b : α) (t : a = b → β) (e : β) (_h : ∀ p, t p = e) : β := e

theorem Eval_ptrSel {α β : Type} {A : RefInv α} {B : RefInv β} (hA : EqSound A)
    {env : SemEnv Value} {ea eb et ee : Exp} {a b : α} {t : a = b → β} {e : β} {h : ∀ p, t p = e}
    (ha : Eval env ea (A a)) (hb : Eval env eb (A b)) (ht : ∀ p : a = b, Eval env et (B (t p)))
    (he : Eval env ee (B e)) :
    Eval env (.if_ (.app .equality [ea, eb]) et ee) (B (ptrSel a b t e h)) :=
  Eval_ifP (Eval_eqSound hA ha hb)
    (fun _ hr hb => by have p := hr hb; have := ht p; rw [h p] at this; exact this)
    (fun _ _ _ => he)

end ConPastel.Translator
