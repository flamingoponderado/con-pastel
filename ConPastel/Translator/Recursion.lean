import ConPastel.Translator.Basic

/-!
# Recursive closures

A `letrec`/`Dletrec` group `funs` binds each name to a `recclosure`.
Applying one evaluates its body in the closure environment extended with
the whole group and the argument. Certificates for recursive Lean functions
are proved by functional induction, using `AppReturns_recclosure` for the
calls.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL

/-! ## Namespace lookups -/

theorem beq_eq_decide_of_decEq {α : Type} [DecidableEq α] (a b : α) :
    (a == b) = decide (a = b) := rfl

@[simp] theorem nsLookup_bind_short {β : Type} (vs : List (VarN × β))
    (ms : List (ModN × Namespace ModN VarN β)) (n : VarN) :
    nsLookup (.bind vs ms) (.short n) = vs.lookup n := rfl

@[simp] theorem nsBind_bind {β : Type} (k : VarN) (x : β) (vs : List (VarN × β))
    (ms : List (ModN × Namespace ModN VarN β)) :
    nsBind k x (.bind vs ms) = .bind ((k, x) :: vs) ms := rfl

theorem nsLookup_nsBind_short {β : Type} (e : Namespace ModN VarN β) (k n : VarN) (x : β) :
    nsLookup (nsBind k x e) (.short n) = if n = k then some x else nsLookup e (.short n) := by
  cases e with
  | bind vs ms =>
    by_cases h : n = k
    · simp [List.lookup, h]
    · have : (n == k) = false := beq_eq_false_iff_ne.mpr h
      simp [List.lookup, h, this]

theorem nsLookup_buildRecEnv {funs : List (VarN × VarN × Exp)} {envC : SemEnv Value}
    {e : Namespace ModN VarN Value} {g : VarN} (hg : g ∈ funs.map (·.1)) :
    nsLookup (buildRecEnv funs envC e) (.short g) = some (.recclosure envC funs g) := by
  unfold buildRecEnv
  suffices ∀ fs : List (VarN × VarN × Exp), g ∈ fs.map (·.1) →
      nsLookup (fs.foldr (fun (name, _, _) rest => nsBind name (.recclosure envC funs name) rest) e)
        (.short g) = some (.recclosure envC funs g) from this funs hg
  intro fs hfs
  induction fs with
  | nil => simp at hfs
  | cons p fs ih =>
    obtain ⟨name, arg, body⟩ := p
    simp only [List.foldr_cons, nsLookup_nsBind_short]
    by_cases h : g = name
    · simp [h]
    · simp only [h, ite_false]
      apply ih
      simpa [h] using hfs

/-! ## Applying a recursive closure -/

/-- The environment a recursive closure's body runs in. -/
def recBodyEnv (envC : SemEnv Value) (funs : List (VarN × VarN × Exp)) (x : VarN)
    (xv : Value) : SemEnv Value :=
  { envC with v := nsBind x xv (buildRecEnv funs envC envC.v) }

theorem AppReturns_recclosure {envC : SemEnv Value} {funs : List (VarN × VarN × Exp)}
    {g x : VarN} {body : Exp} {xv : Value} {Q : Value → Prop}
    (hnodup : (funs.map fun (f, _, _) => f).Nodup) (hfind : findRecFun g funs = some (x, body))
    (h : Eval (recBodyEnv envC funs x xv) body Q) :
    AppReturns (.recclosure envC funs g) xv Q := by
  intro σ s
  obtain ⟨v, refs, hrel, hv⟩ := h σ s
  exact ⟨_, _, by simp [doOpApp, hnodup, hfind]; rfl, v, refs, hrel, hv⟩

/-! ## Lookup steps (for direct lookup proofs) -/

theorem lk_bind_same {β : Type} (k : VarN) (x : β) (e : Namespace ModN VarN β) :
    nsLookup (nsBind k x e) (.short k) = some x := by
  rw [nsLookup_nsBind_short]; simp

theorem lk_bind_ne {β : Type} {k n : VarN} (h : n ≠ k) (x : β) (e : Namespace ModN VarN β) {r : Option β}
    (hr : nsLookup e (.short n) = r) : nsLookup (nsBind k x e) (.short n) = r := by
  rw [nsLookup_nsBind_short]; simp [h, hr]

theorem lk_app_nil {β : Type} (e : Namespace ModN VarN β) (n : VarN) {r : Option β}
    (hr : nsLookup e (.short n) = r) : nsLookup (nsAppend (alistToNs []) e) (.short n) = r := by
  cases e; simpa [nsAppend, alistToNs] using hr

theorem lk_app_same {β : Type} (k : VarN) (x : β) (al : List (VarN × β)) (e : Namespace ModN VarN β) :
    nsLookup (nsAppend (alistToNs ((k, x) :: al)) e) (.short k) = some x := by
  cases e; simp [nsAppend, alistToNs, List.lookup]

theorem lk_app_ne {β : Type} {k n : VarN} (h : n ≠ k) (x : β) (al : List (VarN × β))
    (e : Namespace ModN VarN β) {r : Option β} (hr : nsLookup (nsAppend (alistToNs al) e) (.short n) = r) :
    nsLookup (nsAppend (alistToNs ((k, x) :: al)) e) (.short n) = r := by
  cases e
  have hb : (n == k) = false := beq_eq_false_iff_ne.mpr h
  simpa [nsAppend, alistToNs, List.lookup, hb] using hr

end ConPastel.Translator
