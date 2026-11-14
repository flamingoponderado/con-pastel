import ConPastel.Translator.Prelude
import ConPastel.Semantics.Init

/-!
# Lemmas in the shape the translator emits

Each lemma relates a CakeML construct to the Lean construct it translates,
with invariants applied to Lean terms, so the translator can chain them by
unification.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- Decidable propositions are represented by their truth value. -/
def DEC (p : Prop) [Decidable p] (v : Value) : Prop := BOOL (decide p) v

theorem Eval_ite {α : Type} {A : RefInv α} {env : SemEnv Value} {c : Prop} [Decidable c]
    {ec e₁ e₂ : Exp} {t e : α} (hc : Eval env ec (BOOL (decide c)))
    (h₁ : c → Eval env e₁ (A t)) (h₂ : ¬c → Eval env e₂ (A e)) :
    Eval env (.if_ ec e₁ e₂) (A (if c then t else e)) :=
  Eval_if hc (fun h => by have hc' : c := of_decide_eq_true h; simpa [hc'] using h₁ hc')
    (fun h => by have hc' : ¬c := of_decide_eq_false h; simpa [hc'] using h₂ hc')

theorem Eval_dite {α : Type} {A : RefInv α} {env : SemEnv Value} {c : Prop} [Decidable c]
    {ec e₁ e₂ : Exp} {t : c → α} {e : ¬c → α} (hc : Eval env ec (BOOL (decide c)))
    (h₁ : ∀ h : c, Eval env e₁ (A (t h))) (h₂ : ∀ h : ¬c, Eval env e₂ (A (e h))) :
    Eval env (.if_ ec e₁ e₂) (A (if h : c then t h else e h)) :=
  Eval_if hc (fun h => by have hc' : c := of_decide_eq_true h; simpa [hc'] using h₁ hc')
    (fun h => by have hc' : ¬c := of_decide_eq_false h; simpa [hc'] using h₂ hc')

/-! ## Nat as integers -/

theorem NAT_iff_INT (n : Nat) (v : Value) : NAT n v ↔ INT (n : Int) v := Iff.rfl

theorem Eval_nat_lit (env : SemEnv Value) (n : Nat) :
    Eval env (.lit (.intLit n)) (NAT n) := Eval_lit _ _ _ rfl

theorem Eval_nat_add {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Nat}
    (h₁ : Eval env e₁ (NAT a)) (h₂ : Eval env e₂ (NAT b)) :
    Eval env (.app (.arith .add .intT) [e₁, e₂]) (NAT (a + b)) :=
  Eval_weaken (Eval_int_add h₁ h₂) fun v hv => by simpa [NAT, INT] using hv

theorem Eval_nat_mul {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Nat}
    (h₁ : Eval env e₁ (NAT a)) (h₂ : Eval env e₂ (NAT b)) :
    Eval env (.app (.arith .mul .intT) [e₁, e₂]) (NAT (a * b)) :=
  Eval_weaken (Eval_int_mul h₁ h₂) fun v hv => by simpa [NAT, INT] using hv

theorem Eval_nat_lt {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Nat}
    (h₁ : Eval env e₁ (NAT a)) (h₂ : Eval env e₂ (NAT b)) :
    Eval env (.app (.test (.compare .lt) .intT) [e₁, e₂]) (BOOL (decide (a < b))) :=
  Eval_weaken (Eval_int_cmp .lt h₁ h₂) fun v hv => by
    simpa [(intCmp_spec _ _).1] using hv

theorem Eval_nat_le {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Nat}
    (h₁ : Eval env e₁ (NAT a)) (h₂ : Eval env e₂ (NAT b)) :
    Eval env (.app (.test (.compare .leq) .intT) [e₁, e₂]) (BOOL (decide (a ≤ b))) :=
  Eval_weaken (Eval_int_cmp .leq h₁ h₂) fun v hv => by
    simpa [(intCmp_spec _ _).2.1] using hv

theorem Eval_nat_eq {env : SemEnv Value} {e₁ e₂ : Exp} {a b : Nat}
    (h₁ : Eval env e₁ (NAT a)) (h₂ : Eval env e₂ (NAT b)) :
    Eval env (.app .equality [e₁, e₂]) (BOOL (decide (a = b))) :=
  Eval_weaken (Eval_int_eq h₁ h₂) fun v hv => by simpa [Int.natCast_inj] using hv

/-- `Nat.sub` through the prelude closure bound at `natSubName`. -/
theorem Eval_nat_sub {env : SemEnv Value} {fe e₁ e₂ : Exp} {a b : Nat}
    (hf : Eval env fe (Arrow NAT (Arrow NAT NAT) Nat.sub))
    (h₁ : Eval env e₁ (NAT a)) (h₂ : Eval env e₂ (NAT b)) :
    Eval env (.app .opapp [.app .opapp [fe, e₁], e₂]) (NAT (a - b)) :=
  Eval_app_arrow (Eval_app_arrow hf h₁) h₂

/-! ## Booleans -/

/-- The constructor environment has CakeML's boolean constructors. -/
structure HasBoolCons (envC : Namespace ModN ConN (Nat × Stamp)) : Prop where
  true_ : nsLookup envC (.short (Basis.Pure.MlString.ofString "True")) =
    some (0, .typeStamp (Basis.Pure.MlString.ofString "True") 0)
  false_ : nsLookup envC (.short (Basis.Pure.MlString.ofString "False")) =
    some (0, .typeStamp (Basis.Pure.MlString.ofString "False") 0)

theorem initEnv_hasBoolCons : HasBoolCons ConPastel.initEnv.c := ⟨by decide, by decide⟩

/-- The CakeML expression for a boolean literal. -/
def boolLit (b : Bool) : Exp :=
  .con (some (.short (Basis.Pure.MlString.ofString (if b then "True" else "False")))) []

theorem Eval_bool_lit {env : SemEnv Value} (h : HasBoolCons env.c) (b : Bool) :
    Eval env (boolLit b) (BOOL b) := by
  have hl : nsLookup env.c (.short (Basis.Pure.MlString.ofString (if b then "True" else "False"))) =
      some (([] : List Exp).length,
        .typeStamp (Basis.Pure.MlString.ofString (if b then "True" else "False")) 0) := by
    cases b
    · exact h.false_
    · exact h.true_
  refine Eval_weaken (Eval_con (Ps := []) hl trivial) fun v ⟨vs, hvs, hv⟩ => ?_
  cases hvs
  subst hv
  cases b <;> rfl

/-! ## let with the defining equation as a path condition -/

theorem Eval_let_eq {α β : Type} {A : RefInv α} {B : RefInv β} {env : SemEnv Value} {n : VarN}
    {e₁ e₂ : Exp} {v : α} {b : α → β}
    (h₁ : Eval env e₁ (A v))
    (h₂ : ∀ x, x = v → ∀ xv, A x xv → Eval { v := nsBind n xv env.v, c := env.c } e₂ (B (b x))) :
    Eval env (.let_ (some n) e₁ e₂) (B (b v)) :=
  Eval_let h₁ fun xv hxv => h₂ v rfl xv hxv

/-! ## Recursive closures by well-founded induction -/

/-- A recursive function value refines `f` if, assuming the refinement for
all arguments below `x` in a well-founded relation, it refines `f x`. -/
theorem arrow_of_wf {α β : Type} {A : RefInv α} {B : RefInv β} {r : α → α → Prop}
    (hwf : WellFounded r) {f : α → β} {cl : Value}
    (h : ∀ x, (∀ y, r y x → ∀ yv, A y yv → AppReturns cl yv (B (f y))) →
      ∀ xv, A x xv → AppReturns cl xv (B (f x))) :
    Arrow A B f cl := by
  intro x
  induction x using hwf.induction with
  | _ x ih => exact h x ih

/-- A recursive call: the callee value is the recursive closure, for which the
induction hypothesis gives the refinement at the call's argument. -/
theorem Eval_app_ih {α β : Type} {A : RefInv α} {B : RefInv β} {env : SemEnv Value}
    {ef ex : Exp} {cl : Value} {f : α → β} {y : α}
    (hf : Eval env ef (· = cl)) (hx : Eval env ex (A y))
    (ih : ∀ yv, A y yv → AppReturns cl yv (B (f y))) :
    Eval env (.app .opapp [ef, ex]) (B (f y)) :=
  Eval_app hf hx fun _ yv hfv hy => hfv ▸ ih yv hy

/-! ## Nat case splits -/

/-- `Nat.casesOn n z s` (non-dependent motive) as
`if n = 0 then z else let m = n - 1 in s`. -/
theorem Eval_nat_casesOn {β : Type} {B : RefInv β} {env : SemEnv Value} {en ez es : Exp}
    {mn : VarN} {n : Nat} {z : β} {s : Nat → β}
    (hn : Eval env en (NAT n))
    (hz : n = 0 → Eval env ez (B z))
    (hs : ∀ m, n = m + 1 → ∀ mv, NAT m mv → Eval { v := nsBind mn mv env.v, c := env.c } es (B (s m))) :
    Eval env (.if_ (.app .equality [en, .lit (.intLit 0)]) ez
      (.let_ (some mn) (.app (.arith .sub .intT) [en, .lit (.intLit 1)]) es))
      (B (Nat.casesOn (motive := fun _ => β) n z s)) := by
  refine Eval_if (Eval_nat_eq hn (Eval_nat_lit env 0)) (fun h => ?_) (fun h => ?_)
  · have : n = 0 := of_decide_eq_true h
    subst this
    exact hz rfl
  · have hne : n ≠ 0 := of_decide_eq_false h
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine Eval_let (P := NAT m) (Eval_weaken (Eval_int_sub hn (Eval_lit env _ (INT 1) rfl)) ?_) ?_
    · intro v hv; simp only [INT] at hv; simp [NAT, hv]
    · intro mv hmv; exact hs m rfl mv hmv

/-! ## Unit and thunks -/

def UNIT : RefInv Unit := fun _ v => v = .conv none []

theorem Eval_unit (env : SemEnv Value) : Eval env (.con none []) (UNIT ()) := by
  intro σ s
  refine ⟨.conv none [], [], ⟨0, 0, ?_⟩, rfl⟩
  rw [Flapjack.EvaluateHOL.evaluate]
  simp [doConCheck, buildConv, Flapjack.EvaluateHOL.evaluate]

theorem findRecFun_mem {α β : Type} {n : VarN} :
    ∀ {funs : List (VarN × α × β)} {r : α × β}, findRecFun n funs = some r → n ∈ funs.map (·.1)
  | [], _, h => by simp [findRecFun] at h
  | (f, x, b) :: rest, r, h => by
    simp only [findRecFun] at h
    by_cases hf : f = n
    · simp [hf]
    · simp only [hf, ite_false] at h
      exact List.mem_cons_of_mem _ (findRecFun_mem h)

/-! ## Dependent function invariants, with erased proof arguments -/

/-- Functions taking a proof: the CakeML value takes no argument for it. -/
def PIPROP {p : Prop} {β : p → Type} (B : (h : p) → RefInv (β h)) : RefInv ((h : p) → β h) :=
  fun f v => ∀ h, B h (f h) v

/-- Dependent functions on data. -/
def DARROW {α : Type} {β : α → Type} (A : RefInv α) (B : (x : α) → RefInv (β x)) :
    RefInv ((x : α) → β x) :=
  fun f v => ∀ x xv, A x xv → AppReturns v xv (B x (f x))

theorem Eval_piprop_elim {p : Prop} {β : p → Type} {B : (h : p) → RefInv (β h)} {env : SemEnv Value}
    {e : Exp} {f : (h : p) → β h} (hf : Eval env e (PIPROP B f)) (h : p) : Eval env e (B h (f h)) :=
  Eval_weaken hf fun _ hv => hv h

theorem Eval_piprop_intro {p : Prop} {β : p → Type} {B : (h : p) → RefInv (β h)} {env : SemEnv Value}
    {e : Exp} {f : (h : p) → β h} (hf : ∀ h, Eval env e (B h (f h))) [Nonempty p] :
    Eval env e (PIPROP B f) := by
  intro σ s
  obtain ⟨h⟩ := ‹Nonempty p›
  obtain ⟨v, refs, hrel, hv⟩ := hf h σ s
  exact ⟨v, refs, hrel, fun h' => by simpa using hv⟩

theorem Eval_app_darrow {α : Type} {β : α → Type} {A : RefInv α} {B : (x : α) → RefInv (β x)}
    {env : SemEnv Value} {ef ex : Exp} {f : (x : α) → β x} {x : α}
    (hf : Eval env ef (DARROW A B f)) (hx : Eval env ex (A x)) :
    Eval env (.app .opapp [ef, ex]) (B x (f x)) :=
  Eval_app hf hx fun _ _ hfv hxv => hfv x _ hxv

theorem Eval_fn_darrow {α : Type} {β : α → Type} {A : RefInv α} {B : (x : α) → RefInv (β x)}
    {env : SemEnv Value} {n : VarN} {body : Exp} {f : (x : α) → β x}
    (h : ∀ x xv, A x xv → Eval { env with v := nsBind n xv env.v } body (B x (f x))) :
    Eval env (.fn n body) (DARROW A B f) := by
  apply Eval_fn
  intro x xv hx σ s
  obtain ⟨v, refs, hrel, hv⟩ := h x xv hx σ s
  exact ⟨_, _, rfl, v, refs, hrel, hv⟩

/-! ## Newtypes: structures with one data field -/

/-- A structure with a single data field is represented by that field. -/
def NEWTYPE {S F : Type} (proj : S → F) (A : RefInv F) : RefInv S := fun s v => A (proj s) v

/-- A data argument followed by a proof about it: applying the value to `x`
returns a representation of `f x h` for every proof `h`. -/
def DARROWP {α : Type} {P : α → Prop} {β : (x : α) → P x → Type} (A : RefInv α)
    (B : (x : α) → (h : P x) → RefInv (β x h)) : RefInv ((x : α) → (h : P x) → β x h) :=
  fun f v => ∀ x xv, A x xv → ∀ h, AppReturns v xv (B x h (f x h))

theorem Eval_app_darrowp {α : Type} {P : α → Prop} {β : (x : α) → P x → Type} {A : RefInv α}
    {B : (x : α) → (h : P x) → RefInv (β x h)} {env : SemEnv Value} {ef ex : Exp}
    {f : (x : α) → (h : P x) → β x h} {x : α} (hf : Eval env ef (DARROWP A B f))
    (hx : Eval env ex (A x)) (h : P x) :
    Eval env (.app .opapp [ef, ex]) (B x h (f x h)) :=
  Eval_app hf hx fun _ _ hfv hxv => hfv x _ hxv h

theorem Eval_fn_darrowp {α : Type} {P : α → Prop} {β : (x : α) → P x → Type} {A : RefInv α}
    {B : (x : α) → (h : P x) → RefInv (β x h)} {env : SemEnv Value} {n : VarN} {body : Exp}
    {f : (x : α) → (h : P x) → β x h}
    (hb : ∀ x xv, A x xv → ∀ h, Eval { env with v := nsBind n xv env.v } body (B x h (f x h))) :
    Eval env (.fn n body) (DARROWP A B f) := by
  apply Eval_fn
  intro x xv hx h σ s
  obtain ⟨v, refs, hrel, hv⟩ := hb x xv hx h σ s
  exact ⟨_, _, rfl, v, refs, hrel, hv⟩

/-! ## Bool case splits -/

theorem Eval_bool_rec {β : Type} {B : RefInv β} {env : SemEnv Value} {eb et ef : Exp} {b : Bool}
    {f t : β} (hb : Eval env eb (BOOL b)) (hf : b = false → Eval env ef (B f))
    (ht : b = true → Eval env et (B t)) :
    Eval env (.if_ eb et ef) (B (Bool.rec (motive := fun _ => β) f t b)) :=
  Eval_if hb (fun h => by subst h; exact ht rfl) (fun h => by subst h; exact hf rfl)

/-! ## Casts -/

/-- Transport along an equation is the identity on values. -/
theorem Eval_eqrec {α : Type} {a : α} {motive : (b : α) → a = b → Type}
    {I : (b : α) → (h : a = b) → RefInv (motive b h)} {env : SemEnv Value} {e : Exp}
    {m : motive a rfl} {b : α} (h : a = b) (hm : Eval env e (I a rfl m)) :
    Eval env e (I b h (Eq.rec (motive := motive) m h)) := by
  cases h; exact hm

/-- Bounded list indexing as total indexing with a default (used for `List.get`). -/
theorem list_get_eq_getD {α : Type u} [Inhabited α] (l : List α) (f : Fin l.length) :
    l.get f = l.getD f.val default := by
  simp [List.getD_eq_getElem?_getD]

/-- A recursive call inside a well-founded functional, carrying Lean's own
decreasing proof (the translator reads the proof off; the value is `f y`). -/
def recCall {α : Sort u} {β : α → Sort v} {P : Prop} (f : (a : α) → β a) (y : α) (_h : P) : β y := f y

/-- `Option.get` (dependent on its proof) as `Option.getD` for inhabited types. -/
theorem option_get_eq_getD {α : Type u} [Inhabited α] (o : Option α) (h : o.isSome) :
    o.get h = o.getD default := by
  cases o with
  | none => simp at h
  | some x => rfl

end ConPastel.Translator
