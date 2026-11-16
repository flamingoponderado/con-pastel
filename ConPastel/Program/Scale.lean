import ConPastel.Program.ConCheck
import ConPastel.Translator.Recursion

/-!
# Side conditions of large programs, without kernel string comparisons

Comparing two `ofString "…"` names in the kernel decodes both literals
(milliseconds and megabytes each), so `cake_program` never decides
string (in)equalities over the whole group. Instead:

* distinctness of a list of names is checked on their character codes: the
  names are given as character lists, `xs = names.map (ofString ∘ String.ofList)`
  holds by unfolding the literals, and the codes are checked sorted
  (`sortedN`) or pairwise distinct (`distinctN`) — natural-number work only;
* lookups (`findRecFun`, the group's `buildRecEnv`, the constructor
  environment) follow from membership — a structural proof — and distinctness;
* the constructor-arity side condition is a derivation `COk tbl e` whose
  `con` steps carry membership proofs into the arity table.
-/

namespace ConPastel.Program
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString ConPastel.Translator

/-! ## Distinctness from character codes -/

def eqN : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && eqN as bs
  | _, _ => false

theorem eqN_iff : ∀ a b : List Nat, eqN a b = true ↔ a = b
  | [], [] => by simp [eqN]
  | [], _ :: _ => by simp [eqN]
  | _ :: _, [] => by simp [eqN]
  | a :: as, b :: bs => by simp [eqN, eqN_iff as bs]

def lexLtN : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => Nat.blt a b || (Nat.beq a b && lexLtN as bs)

theorem lexLtN_irrefl : ∀ a : List Nat, lexLtN a a = false
  | [] => rfl
  | a :: as => by
    have h : Nat.blt a a = false := by rw [Bool.eq_false_iff]; simp [Nat.blt_eq]
    simp [lexLtN, h, lexLtN_irrefl as]

theorem lexLtN_trans : ∀ a b c : List Nat, lexLtN a b = true → lexLtN b c = true → lexLtN a c = true
  | [], [], _, h, _ => by simp [lexLtN] at h
  | [], _ :: _, [], _, h => by simp [lexLtN] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [lexLtN] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLtN] at h
  | a :: as, b :: bs, c :: cs, h1, h2 => by
    simp only [lexLtN, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact .inl (by omega)
    · exact .inl h1
    · exact .inl h2
    · exact .inr ⟨rfl, lexLtN_trans as bs cs h1 h2⟩

def sortedN : List (List Nat) → Bool
  | a :: b :: r => lexLtN a b && sortedN (b :: r)
  | _ => true

theorem sortedN_head : ∀ (a : List Nat) (l : List (List Nat)), sortedN (a :: l) = true →
    ∀ b ∈ l, lexLtN a b = true
  | _, [], _, b, hb => by simp at hb
  | a, c :: l, h, b, hb => by
    simp only [sortedN, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.1
    · exact lexLtN_trans _ _ _ h.1 (sortedN_head c l h.2 b hb)

theorem nodup_of_sortedN : ∀ l : List (List Nat), sortedN l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  | a :: b :: r, h => by
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_of_sortedN (b :: r) ?_⟩
    · have := sortedN_head a (b :: r) h a hm
      rw [lexLtN_irrefl] at this; exact absurd this (by decide)
    · simp only [sortedN, Bool.and_eq_true] at h; exact h.2

def distinctN : List (List Nat) → Bool
  | [] => true
  | a :: r => r.all (fun b => !eqN a b) && distinctN r

theorem nodup_of_distinctN : ∀ l : List (List Nat), distinctN l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: r, h => by
    simp only [distinctN, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_of_distinctN r h.2⟩
    have := h.1 a hm
    rw [show eqN a a = true from (eqN_iff a a).mpr rfl] at this
    exact absurd this (by decide)

def charKey (cs : List Char) : List Nat := cs.map fun c => c.toNat % 256

def mlKey (s : MlString) : List Nat := s.explode.map BitVec.toNat

theorem mlKey_ofString_ofList (cs : List Char) : mlKey (ofString (String.ofList cs)) = charKey cs := by
  simp [mlKey, ofString, charKey, MlString.explode, Function.comp_def, BitVec.toNat_ofNat]

theorem nodup_of_map_nodup {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun hm => h.1 (List.mem_map_of_mem hm), nodup_of_map_nodup f h.2⟩

theorem nodup_names_of_keys (xs : List MlString) (names : List (List Char))
    (h1 : xs = names.map fun cs => ofString (String.ofList cs)) (h2 : (names.map charKey).Nodup) :
    xs.Nodup := by
  subst h1
  apply nodup_of_map_nodup mlKey
  rw [List.map_map]
  have : (mlKey ∘ fun cs => ofString (String.ofList cs)) = charKey := funext mlKey_ofString_ofList
  rw [this]; exact h2

theorem nodup_names_sorted (xs : List MlString) (names : List (List Char))
    (h1 : xs = names.map fun cs => ofString (String.ofList cs)) (h2 : sortedN (names.map charKey) = true) :
    xs.Nodup := nodup_names_of_keys xs names h1 (nodup_of_sortedN _ h2)

theorem nodup_names_distinct (xs : List MlString) (names : List (List Char))
    (h1 : xs = names.map fun cs => ofString (String.ofList cs)) (h2 : distinctN (names.map charKey) = true) :
    xs.Nodup := nodup_names_of_keys xs names h1 (nodup_of_distinctN _ h2)

/-! ## Lookups from membership -/

theorem lookup_of_mem_nodup {β : Type} : ∀ {l : List (MlString × β)} {k : MlString} {v : β},
    (l.map Prod.fst).Nodup → (k, v) ∈ l → l.lookup k = some v
  | [], _, _, _, hm => by simp at hm
  | (a, b) :: l, k, v, hnd, hm => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with h | h
    · cases h; simp [List.lookup]
    · have hka : k ≠ a := by
        rintro rfl; exact hnd.1 (List.mem_map_of_mem (f := Prod.fst) h)
      have : (k == a) = false := beq_eq_false_iff_ne.mpr hka
      simp only [List.lookup, this]
      exact lookup_of_mem_nodup hnd.2 h

/-- A constructor lookup in a flat constructor environment. -/
theorem nsLookup_c_of_mem {envC : Namespace ModN ConN (Nat × Stamp)} {l : List (ConN × Nat × Stamp)}
    (hc : envC = .bind l []) (hnd : (l.map Prod.fst).Nodup) {c : ConN} {v : Nat × Stamp}
    (hm : (c, v) ∈ l) : nsLookup envC (.short c) = some v := by
  subst hc; rw [nsLookup_bind_short]; exact lookup_of_mem_nodup hnd hm

theorem findRecFun_of_mem {α β : Type} : ∀ {funs : List (VarN × α × β)} {g : VarN} {x : α} {b : β},
    List.Nodup (List.map (fun p => p.1) funs) → (g, x, b) ∈ funs → findRecFun g funs = some (x, b)
  | [], _, _, _, _, hm => by simp at hm
  | (f, y, c) :: fs, g, x, b, hnd, hm => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with h | h
    · cases h; simp [findRecFun]
    · have hgf : f ≠ g := by
        rintro rfl; exact hnd.1 (List.mem_map_of_mem (f := fun p => p.1) h)
      simp only [findRecFun, hgf, ite_false]
      exact findRecFun_of_mem hnd.2 h

theorem name_mem_of_mem {α β : Type} {funs : List (VarN × α × β)} {g : VarN} {x : α} {b : β}
    (h : (g, x, b) ∈ funs) : g ∈ funs.map (·.1) :=
  List.mem_map_of_mem (f := fun p => p.1) h

theorem groupLookup_of_mem {funs : List (VarN × VarN × Exp)} {envC : SemEnv Value} {g x : VarN} {b : Exp}
    (h : (g, x, b) ∈ funs) :
    nsLookup (buildRecEnv funs envC envC.v) (.short g) = some (.recclosure envC funs g) :=
  nsLookup_buildRecEnv (name_mem_of_mem h)

/-! ## Membership steps (kept explicit for proof construction) -/

theorem mem_head {α : Type} (a : α) (l : List α) : a ∈ a :: l := List.mem_cons_self
theorem mem_tail {α : Type} (a b : α) (l : List α) (h : a ∈ l) : a ∈ b :: l := List.mem_cons_of_mem b h
theorem mem_appL {α : Type} (a : α) (l r : List α) (h : a ∈ l) : a ∈ l ++ r := List.mem_append_left r h
theorem mem_appR {α : Type} (a : α) (l r : List α) (h : a ∈ r) : a ∈ l ++ r := List.mem_append_right l h

/-! ## The constructor-arity derivation -/

mutual
inductive COk (tbl : List (ConN × Nat)) : Exp → Prop
  | raise (e : Exp) : COk tbl e → COk tbl (.raise e)
  | handle (e : Exp) (cs : List (Pat × Exp)) : COk tbl e → COkC tbl cs → COk tbl (.handle e cs)
  | lit (l : Lit) : COk tbl (.lit l)
  | conNone (es : List Exp) : COkL tbl es → COk tbl (.con none es)
  | conShort (c : ConN) (es : List Exp) : (c, es.length) ∈ tbl → COkL tbl es →
      COk tbl (.con (some (.short c)) es)
  | var (x : Ident ModN VarN) : COk tbl (.var x)
  | fn (x : VarN) (e : Exp) : COk tbl e → COk tbl (.fn x e)
  | app (op : Op) (es : List Exp) : COkL tbl es → COk tbl (.app op es)
  | log (op : Lop) (a b : Exp) : COk tbl a → COk tbl b → COk tbl (.log op a b)
  | if_ (a b c : Exp) : COk tbl a → COk tbl b → COk tbl c → COk tbl (.if_ a b c)
  | mat (e : Exp) (cs : List (Pat × Exp)) : COk tbl e → COkC tbl cs → COk tbl (.mat e cs)
  | let_ (x : Option VarN) (a b : Exp) : COk tbl a → COk tbl b → COk tbl (.let_ x a b)
  | letrec (fs : List (VarN × VarN × Exp)) (b : Exp) : COkF tbl fs → COk tbl b → COk tbl (.letrec fs b)
  | tannot (e : Exp) (t : AstT) : COk tbl e → COk tbl (.tannot e t)
  | lannot (e : Exp) (l : Flapjack.Misc.Location.Locs) : COk tbl e → COk tbl (.lannot e l)
inductive COkL (tbl : List (ConN × Nat)) : List Exp → Prop
  | nil : COkL tbl []
  | cons (e : Exp) (es : List Exp) : COk tbl e → COkL tbl es → COkL tbl (e :: es)
inductive COkC (tbl : List (ConN × Nat)) : List (Pat × Exp) → Prop
  | nil : COkC tbl []
  | cons (p : Pat) (e : Exp) (cs : List (Pat × Exp)) : COk tbl e → COkC tbl cs → COkC tbl ((p, e) :: cs)
inductive COkF (tbl : List (ConN × Nat)) : List (VarN × VarN × Exp) → Prop
  | nil : COkF tbl []
  | cons (f x : VarN) (e : Exp) (fs : List (VarN × VarN × Exp)) : COk tbl e → COkF tbl fs →
      COkF tbl ((f, x, e) :: fs)
end

mutual
theorem conOk_of_COk {tbl : List (ConN × Nat)} (hnd : (tbl.map Prod.fst).Nodup) :
    ∀ {e : Exp}, COk tbl e → conOk tbl e = true
  | _, .raise _ h => by simp only [conOk]; exact conOk_of_COk hnd h
  | _, .handle _ _ h hc => by simp [conOk, conOk_of_COk hnd h, conOkClauses_of_COkC hnd hc]
  | _, .lit _ => by simp [conOk]
  | _, .conNone _ hl => by simp [conOk, conHeadOk, conOkList_of_COkL hnd hl]
  | _, .conShort _ _ hm hl => by
    simp [conOk, conHeadOk, lookup_of_mem_nodup hnd hm, conOkList_of_COkL hnd hl]
  | _, .var _ => by simp [conOk]
  | _, .fn _ _ h => by simp only [conOk]; exact conOk_of_COk hnd h
  | _, .app _ _ hl => by simp only [conOk]; exact conOkList_of_COkL hnd hl
  | _, .log _ _ _ ha hb => by simp [conOk, conOk_of_COk hnd ha, conOk_of_COk hnd hb]
  | _, .if_ _ _ _ ha hb hc => by
    simp [conOk, conOk_of_COk hnd ha, conOk_of_COk hnd hb, conOk_of_COk hnd hc]
  | _, .mat _ _ h hc => by simp [conOk, conOk_of_COk hnd h, conOkClauses_of_COkC hnd hc]
  | _, .let_ _ _ _ ha hb => by simp [conOk, conOk_of_COk hnd ha, conOk_of_COk hnd hb]
  | _, .letrec _ _ hf hb => by simp [conOk, conOk_of_COk hnd hb, conOkFuns_of_COkF hnd hf]
  | _, .tannot _ _ h => by simp only [conOk]; exact conOk_of_COk hnd h
  | _, .lannot _ _ h => by simp only [conOk]; exact conOk_of_COk hnd h
theorem conOkList_of_COkL {tbl : List (ConN × Nat)} (hnd : (tbl.map Prod.fst).Nodup) :
    ∀ {es : List Exp}, COkL tbl es → conOkList tbl es = true
  | _, .nil => by simp [conOkList]
  | _, .cons _ _ h hl => by simp [conOkList, conOk_of_COk hnd h, conOkList_of_COkL hnd hl]
theorem conOkClauses_of_COkC {tbl : List (ConN × Nat)} (hnd : (tbl.map Prod.fst).Nodup) :
    ∀ {cs : List (Pat × Exp)}, COkC tbl cs → conOkClauses tbl cs = true
  | _, .nil => by simp [conOkClauses]
  | _, .cons _ _ _ h hc => by simp [conOkClauses, conOk_of_COk hnd h, conOkClauses_of_COkC hnd hc]
theorem conOkFuns_of_COkF {tbl : List (ConN × Nat)} (hnd : (tbl.map Prod.fst).Nodup) :
    ∀ {fs : List (VarN × VarN × Exp)}, COkF tbl fs → conOkFuns tbl fs = true
  | _, .nil => by simp [conOkFuns]
  | _, .cons _ _ _ _ h hf => by simp [conOkFuns, conOk_of_COk hnd h, conOkFuns_of_COkF hnd hf]
end

theorem COkF_append {tbl : List (ConN × Nat)} :
    ∀ {a b : List (VarN × VarN × Exp)}, COkF tbl a → COkF tbl b → COkF tbl (a ++ b)
  | _, _, .nil, hb => hb
  | _, _, .cons _ _ _ _ h ha, hb => .cons _ _ _ _ h (COkF_append ha hb)

/-- `tds.all checkDupCtors` one type at a time. -/
theorem all_cons_of {α : Type} {p : α → Bool} {a : α} {l : List α} (h : p a = true)
    (hl : l.all p = true) : (a :: l).all p = true := by simp [h, hl]

theorem checkDupCtors_of {tv : List TvarN} {tn : TypeN} {cs : List (ConN × List AstT)}
    (h : (cs.map Prod.fst).Nodup) : checkDupCtors (tv, tn, cs) = true := by
  simp [checkDupCtors, h]

end ConPastel.Program
