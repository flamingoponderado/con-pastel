import ConPastel.Leche.KernelTypes
import ConPastel.Translator.EqType

/-!
# Sharing: con-leche's pointer-first equality in CakeML

con-leche's executed equalities (`Name/Level/Literal/Expr.decEqPtr`,
`Expr.beqMemo`) replace the structural ones through `@[csimp]`, and they read
object identity only through `Init.Util`'s `withPtrEq`, `withPtrEqDecEq` and
`withPtrAddr` (wrapped as `ConLeche.ptrDecEq` and `ConLeche.Expr.withAddr`),
whose contracts admit *any* answer that is sound: `true` only for equal
arguments, and any address.

CakeML has no pointer test, but its `=` is structural equality whose compiled
code (`Equal_code`, `data_to_wordScript.sml`) returns at once on identical
pointers, at every level of the descent. So here:

* `exprEqB` and its siblings are primitives compiled to CakeML's `=`;
* a pointer test is the cached hash comparison followed by `=` (equal terms
  have equal hashes, so `=` only ever runs on likely-equal pairs);
* an address is the cached hash (`withPtrAddr` allows any value);
* the `@[csimp]` swaps to the pointer-first equalities are replacements.

The primitives' certificates rest on `EqType` (`ConPastel.Translator.EqType`):
CakeML's structural equality on the representations of these datatypes
decides equality of the values (`cake_eqtype`).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.all false

namespace ConPastel.Impl
open ConLeche

/-- CakeML's `=` on expressions (a primitive): structural equality. -/
def exprEqB (a b : Expr) : Bool := @decide (a = b) (Expr.decEq a b)
/-- CakeML's `=` on names. -/
def nameEqB (a b : Name) : Bool := @decide (a = b) (Name.decEq a b)
/-- CakeML's `=` on levels. -/
def levelEqB (a b : Level) : Bool := @decide (a = b) (Level.decEq a b)
/-- CakeML's `=` on literals. -/
def literalEqB (a b : Literal) : Bool := @decide (a = b) (Literal.decEq a b)

theorem exprEqB_sound {a b : Expr} (h : exprEqB a b = true) : a = b := of_decide_eq_true h
theorem nameEqB_sound {a b : Name} (h : nameEqB a b = true) : a = b := of_decide_eq_true h
theorem levelEqB_sound {a b : Level} (h : levelEqB a b = true) : a = b := of_decide_eq_true h
theorem literalEqB_sound {a b : Literal} (h : literalEqB a b = true) : a = b := of_decide_eq_true h

/-! ## Pointer tests and addresses -/

theorem data_ne {a b : Expr} (h : (a.data == b.data) = false) : a ≠ b := by
  intro e; subst e; simp at h

/-! ### Equality on deep terms

CakeML's `=` returns at once on identical pointers, but on two equal terms
built separately it walks the whole *tree*: exponential in the depth of a
DAG.  So `=` runs only on shallow terms (`depthP ≤ eqSmall`, whose trees are
small); a deep pair goes through con-leche's own memoised descent
(`Expr.beqDec`), whose child step (`enterBeqD` below) applies the same gate.
The descent's memo entries are verified by `=` against the stored pair: both
sides of such a test are nodes of the same term. -/

/-- The depth up to which CakeML's `=` decides expression equality. -/
def eqSmall : Nat := 8

/-- Expression equality as the pointer tests run it: the cached words, then
`=` on a shallow pair and the memoised descent on a deep one. -/
def exprEqD (a b : Expr) : Bool :=
  a.data == b.data && (if a.depthP ≤ eqSmall then exprEqB a b else @decide (a = b) (Expr.beqDec a b))

theorem exprEqD_iff (a b : Expr) : exprEqD a b = true ↔ a = b := by
  unfold exprEqD
  constructor
  · intro h
    simp only [Bool.and_eq_true] at h
    obtain ⟨_, h⟩ := h
    by_cases hs : a.depthP ≤ eqSmall
    · rw [if_pos hs] at h; exact exprEqB_sound h
    · rw [if_neg hs] at h; exact @of_decide_eq_true _ (Expr.beqDec a b) h
  · intro e; subst e
    simp only [beq_self_eq_true, Bool.true_and]
    by_cases hs : a.depthP ≤ eqSmall
    · rw [if_pos hs]; simp [exprEqB]
    · rw [if_neg hs]; simp

/-- The pointer test at `Expr`: the depth-gated equality (a complete
decision, so the continuation is never needed). -/
theorem ptrDecEq_expr (a b : Expr) (k : Unit → Decidable (a = b)) :
    ConLeche.ptrDecEq a b k =
      if h : exprEqD a b = true then isTrue ((exprEqD_iff a b).mp h)
      else isFalse (fun e => h ((exprEqD_iff a b).mpr e)) :=
  Subsingleton.elim _ _

theorem withPtrEq_expr (a b : Expr) (k : Unit → Bool) (h : a = b → k () = true) :
    withPtrEq a b k h = (exprEqD a b || k ()) := by
  show k () = _
  by_cases he : exprEqD a b = true
  · rw [h ((exprEqD_iff a b).mp he)]; simp
  · simp [he]

/-- `probeHit` with the stored pair verified by CakeML's `=`. -/
def probeHitD (m : Expr.BeqMap) (key : Nat) (pa pb : USize) (a b : Expr) :
    { h : Bool // h = true → a = b } :=
  let p := m.getD key Expr.EqPair.dflt
  if p.pa == pa && p.pb == pb then
    if h1 : exprEqB p.fst a = true then
      if h2 : exprEqB p.snd b = true then
        ⟨true, fun _ => (exprEqB_sound h1).symm.trans (p.eq.trans (exprEqB_sound h2))⟩
      else ⟨false, fun h => Bool.noConfusion h⟩
    else ⟨false, fun h => Bool.noConfusion h⟩
  else ⟨false, fun h => Bool.noConfusion h⟩

/-- The child step of con-leche's memoised descent (`Expr.enterBeq`), with
identity read as above: the cached words, `=` on a shallow pair, and on a deep
one the memo probe and the descent.  (con-leche's own step reads an address
match as identity; here an address is the hash, so that would be `=` on every
equal pair.) -/
def enterBeqD (st : Expr.BeqOk) (a b : Expr) (rec : Expr.BeqOk → Expr.BeqOutX a b) :
    Expr.BeqOutX a b :=
  if h : a.data != b.data then .no (fun e => by subst e; simp at h)
  else if a.depthP ≤ eqSmall then
    .mk (if h : exprEqB a b = true then isTrue (exprEqB_sound h)
         else isFalse (fun e => h (by subst e; exact decide_eq_true rfl))) st
  else if !Expr.beqRecursive a then rec st
  else
    let pa := a.data.toUSize
    let pb := b.data.toUSize
    let hit : { h : Bool // h = true → a = b } :=
      match st.1 with
      | .table m => probeHitD m (Expr.beqKey pa pb) pa pb a b
      | _ => ⟨false, fun h => Bool.noConfusion h⟩
    if hh : hit.1 then .yes st (hit.2 hh)
    else Squash.lift (rec st) fun r =>
      if h : r.1.ok then
        .yes ⟨r.1.recordEq a b pa pb (r.2.mp h), Expr.BeqSt.record_ok ..⟩ (r.2.mp h)
      else Quot.mk _ r

theorem enterBeq_eq_D (st : Expr.BeqOk) (a b : Expr) (rec : Expr.BeqOk → Expr.BeqOutX a b) :
    Expr.enterBeq st a b rec = enterBeqD st a b rec := Subsingleton.elim _ _

theorem withAddr_expr {β : Type v} [Subsingleton β] (a : Expr) (k : USize → β) :
    ConLeche.Expr.withAddr a k = k a.data.toUSize :=
  Subsingleton.elim _ _

/-! ## The `@[csimp]` swaps, as replacements -/

/-- `Name`, `Level` and `Literal` equality is CakeML's `=` (small terms). -/
theorem name_decEq_eq (a b : Name) : Name.decEq a b =
    if h : nameEqB a b = true then isTrue (nameEqB_sound h)
    else isFalse (fun e => h (by subst e; exact decide_eq_true rfl)) := Subsingleton.elim _ _
theorem level_decEq_eq (a b : Level) : Level.decEq a b =
    if h : levelEqB a b = true then isTrue (levelEqB_sound h)
    else isFalse (fun e => h (by subst e; exact decide_eq_true rfl)) := Subsingleton.elim _ _
theorem literal_decEq_eq (a b : Literal) : Literal.decEq a b =
    if h : literalEqB a b = true then isTrue (literalEqB_sound h)
    else isFalse (fun e => h (by subst e; exact decide_eq_true rfl)) := Subsingleton.elim _ _
theorem expr_decEq_eq (a b : Expr) : Expr.decEq a b = Expr.decEqPtr a b := Subsingleton.elim _ _
theorem expr_beq_eq (a b : Expr) : Expr.beq a b = Expr.beqMemo a b := by
  rw [Expr.beq_eq_beqMemo]

/-- con-leche's field-read fast paths (`@[csimp]`): `looseBVarsBounded k e`
and `hasFvar e` walk the whole term, exponential on a shared DAG; the fast
versions read the cached ranges (`bvarB`, `fvarB`). -/
theorem looseBVarsBounded_eq_fast (k : Nat) (e : Expr) :
    Expr.looseBVarsBounded k e = Expr.looseBVarsBoundedFast k e := by
  rw [Expr.looseBVarsBounded_eq_looseBVarsBoundedFast]
theorem hasFvar_eq_fast (e : Expr) : Expr.hasFvar e = Expr.hasFvarFast e := by
  rw [Expr.hasFvar_eq_hasFvarFast]

/-- con-leche's declaration comparison against the pinned basis (`andPinOk`):
the fast versions compare the declarations in place rather than building and
comparing their canonical forms (`canon`), which walks every expression. -/
theorem constantVal_canonEq_eq (a b : ConstantVal) :
    ConstantVal.canonEq a b = ConstantVal.canonEqFast a b := by
  rw [ConstantVal.canonEq_eq_canonEqFast]
theorem constantInfo_canonEq_eq (a b : ConstantInfo) :
    ConstantInfo.canonEq a b = ConstantInfo.canonEqFast a b := by
  rw [ConstantInfo.canonEq_eq_canonEqFast]
theorem canonEqList_eq (a b : List ConstantInfo) : canonEqList a b = canonEqListFast a b := by
  rw [canonEqList_eq_canonEqListFast]

/-- `mkBvar i` hands out `bvarPool[i]`, a static table in Lean's runtime. In the
translation a top-level constant is a thunk, evaluated at every use, so each
`mkBvar` would rebuild (and hash) all 4096 pooled nodes: build the node. -/
def mkBvarD (i : Nat) : Expr := .bvar i
theorem mkBvar_eq_D (i : Nat) : Expr.mkBvar i = mkBvarD i := Expr.mkBvar_eq i

end ConPastel.Impl

/-! ## The equality primitives -/

namespace ConPastel.Impl
open ConPastel.Translator

-- the datatypes of `ConPastel.Leche.KernelTypes`, in registration order
example : ConPastel.CakeT.t2.ty = ConLeche.Name := rfl
example : ConPastel.CakeT.t3.ty = ConLeche.Level := rfl
example : ConPastel.CakeT.t4.ty = ConLeche.Literal := rfl
example : ConPastel.CakeT.t5.ty = ConLeche.Expr := rfl

theorem eqType_name : EqType ConPastel.CakeT.t2.cakeInv := by cake_eqtype
theorem eqType_level : EqType ConPastel.CakeT.t3.cakeInv := by cake_eqtype [eqType_name]
theorem eqType_literal : EqType ConPastel.CakeT.t4.cakeInv := by cake_eqtype
theorem eqType_expr : EqType ConPastel.CakeT.t5.cakeInv := by
  cake_eqtype [eqType_name, eqType_level, eqType_literal]

end ConPastel.Impl

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive ConPastel.Impl.exprEqB (Exp.fn (ofString "b") (.app .equality [V "p", V "b"])) by
  intro envC funs hnodup hfind _ _ _
  exact primEq_cert ConPastel.Impl.eqType_expr (fun x y => by simp [ConPastel.Impl.exprEqB]) envC funs _ hnodup hfind

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive ConPastel.Impl.nameEqB (Exp.fn (ofString "b") (.app .equality [V "p", V "b"])) by
  intro envC funs hnodup hfind _ _ _
  exact primEq_cert ConPastel.Impl.eqType_name (fun x y => by simp [ConPastel.Impl.nameEqB]) envC funs _ hnodup hfind

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive ConPastel.Impl.levelEqB (Exp.fn (ofString "b") (.app .equality [V "p", V "b"])) by
  intro envC funs hnodup hfind _ _ _
  exact primEq_cert ConPastel.Impl.eqType_level (fun x y => by simp [ConPastel.Impl.levelEqB]) envC funs _ hnodup hfind

open ConPastel.Translator Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString in
cake_primitive ConPastel.Impl.literalEqB (Exp.fn (ofString "b") (.app .equality [V "p", V "b"])) by
  intro envC funs hnodup hfind _ _ _
  exact primEq_cert ConPastel.Impl.eqType_literal (fun x y => by simp [ConPastel.Impl.literalEqB]) envC funs _ hnodup hfind

cake_rewrite ConPastel.Impl.ptrDecEq_expr
cake_rewrite ConPastel.Impl.withPtrEq_expr
cake_rewrite ConPastel.Impl.name_decEq_eq
cake_rewrite ConPastel.Impl.level_decEq_eq
cake_rewrite ConPastel.Impl.literal_decEq_eq
cake_rewrite ConPastel.Impl.withAddr_expr

cake_replace ConLeche.Expr.decEq ConLeche.Expr.decEqPtr ConPastel.Impl.expr_decEq_eq
cake_replace ConLeche.Expr.beq ConLeche.Expr.beqMemo ConPastel.Impl.expr_beq_eq
cake_replace ConLeche.Expr.enterBeq ConPastel.Impl.enterBeqD ConPastel.Impl.enterBeq_eq_D
cake_replace ConLeche.Expr.looseBVarsBounded ConLeche.Expr.looseBVarsBoundedFast
  ConPastel.Impl.looseBVarsBounded_eq_fast
cake_replace ConLeche.Expr.hasFvar ConLeche.Expr.hasFvarFast ConPastel.Impl.hasFvar_eq_fast
cake_replace ConLeche.Expr.mkBvar ConPastel.Impl.mkBvarD ConPastel.Impl.mkBvar_eq_D
cake_replace ConLeche.ConstantVal.canonEq ConLeche.ConstantVal.canonEqFast ConPastel.Impl.constantVal_canonEq_eq
cake_replace ConLeche.ConstantInfo.canonEq ConLeche.ConstantInfo.canonEqFast ConPastel.Impl.constantInfo_canonEq_eq
cake_replace ConLeche.canonEqList ConLeche.canonEqListFast ConPastel.Impl.canonEqList_eq

-- the equality memo of `Expr.beqMemo` (`beqGoX`)
namespace ConPastel.Leche
cake_datatype (ConLeche.Expr.EqPair)
cake_datatype (Std.DHashMap.Internal.AssocList Nat fun (x : Nat) => ConLeche.Expr.EqPair)
cake_datatype (Std.DHashMap.Raw Nat fun (x : Nat) => ConLeche.Expr.EqPair)
cake_datatype (ConLeche.Expr.BeqSt)
cake_datatype (Option (Std.DHashMap.Internal.AssocList Nat fun (x : Nat) => ConLeche.Expr.EqPair))
end ConPastel.Leche

/-! ## Memoised walks

con-leche runs its walks over expressions as memoised walks (`*XP`), whose
memo types are indexed by terms; the translation runs their plain
specifications (`*P`, `resTerm_eq` & co. in `ConPastel.Translator.Replace`),
which are exponential on a shared DAG. The walks the tower fixtures exercise
are memoised here instead, with a closed memo type (`ExprMemo`) whose entries
are checked by CakeML's `=` and proved correct against the specifications. -/

namespace ConPastel.Impl
open ConLeche

/-! ## Memo tables for walks over shared expressions -/

/-- A memo table: a binary trie on the low bits of an expression's hash, with
association lists of `(node, value)` at the leaves. Correctness never depends
on where an entry is (`ExprMemo.All`); the key only makes lookups short. -/
inductive ExprMemo (α : Type) where
  | leaf (l : List (Expr × α))
  | node (l r : ExprMemo α)

namespace ExprMemo
variable {α : Type}

/-- The trie's key bits for `e`: low bits of its hash (the top half of the
packed `data` word; the low half holds the variable ranges). -/
def key (e : Expr) : Nat := (e.data.toNat / 4294967296) % 65536

def findL (e : Expr) : List (Expr × α) → Option α
  | [] => none
  | (x, v) :: t => if exprEqD x e then some v else findL e t

/-- The value stored for (a node equal to) `e`: the data words first, then
CakeML's `=` (at once on the same pointer). -/
def find? (e : Expr) : ExprMemo α → Nat → Option α
  | .leaf l, _ => findL e l
  | .node a b, k => if k % 2 = 0 then find? e a (k / 2) else find? e b (k / 2)

/-- Store `v` for `e` (at depth `d`, the key's next bit choosing the branch). -/
def insert (e : Expr) (v : α) : Nat → ExprMemo α → Nat → ExprMemo α
  | 0, .leaf l, _ => .leaf ((e, v) :: l)
  | 0, t@(.node ..), _ => t
  | d + 1, .leaf l, k =>
    if k % 2 = 0 then .node (insert e v d (.leaf l) (k / 2)) (.leaf [])
    else .node (.leaf l) (insert e v d (.leaf []) (k / 2))
  | d + 1, .node a b, k =>
    if k % 2 = 0 then .node (insert e v d a (k / 2)) b
    else .node a (insert e v d b (k / 2))

/-- Every entry satisfies `P`. -/
def All (P : Expr → α → Prop) : ExprMemo α → Prop
  | .leaf l => ∀ p ∈ l, P p.1 p.2
  | .node a b => All P a ∧ All P b

theorem findL_sound {P : Expr → α → Prop} {e : Expr} :
    ∀ {l : List (Expr × α)} {v : α}, (∀ p ∈ l, P p.1 p.2) → findL e l = some v → P e v
  | [], _, _, h => by simp [findL] at h
  | (x, w) :: t, v, hl, h => by
    simp only [findL] at h
    split at h
    · rename_i hx; cases h; have := (exprEqD_iff x e).mp hx; subst this
      exact hl (x, _) (by simp)
    · exact findL_sound (fun p hp => hl p (by simp [hp])) h

theorem find?_sound {P : Expr → α → Prop} {e : Expr} :
    ∀ {t : ExprMemo α} {k : Nat} {v : α}, All P t → find? e t k = some v → P e v
  | .leaf l, _, _, ht, h => findL_sound ht h
  | .node a b, k, v, ht, h => by
    simp only [find?] at h
    split at h
    · exact find?_sound ht.1 h
    · exact find?_sound ht.2 h

theorem insert_all {P : Expr → α → Prop} {e : Expr} {v : α} (hv : P e v) :
    ∀ {d : Nat} {t : ExprMemo α} {k : Nat}, All P t → All P (insert e v d t k)
  | 0, .leaf l, _, ht => by
    intro p hp; simp at hp
    rcases hp with rfl | hp
    · exact hv
    · exact ht _ hp
  | 0, .node _ _, _, ht => ht
  | d + 1, .leaf l, k, ht => by
    unfold insert
    split
    · exact ⟨insert_all hv ht, by simp [All]⟩
    · exact ⟨ht, insert_all hv (by simp [All])⟩
  | d + 1, .node a b, k, ht => by
    unfold insert
    split
    · exact ⟨insert_all hv ht.1, ht.2⟩
    · exact ⟨ht.1, insert_all hv ht.2⟩

end ExprMemo

/-! ## `mentionsAnyConstP`, memoised -/

/-- `mentionsAnyConstP names`, with a memo of the compound nodes' answers. -/
def macM (names : List Name) (t : ExprMemo Bool) (e : Expr) : Bool × ExprMemo Bool :=
  match e with
  | .bvar .. | .sort .. | .lit .. => (false, t)
  | .const n .. => (names.contains n, t)
  | .fvar _ ty .. =>
    match t.find? e (ExprMemo.key e) with
    | some b => (b, t)
    | none =>
      let r := macM names t ty
      (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))
  | .app f a .. =>
    match t.find? e (ExprMemo.key e) with
    | some b => (b, t)
    | none =>
      let r1 := macM names t f
      let r := if r1.1 then (true, r1.2) else macM names r1.2 a
      (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))
  | .lam ty body .. | .forallE ty body .. =>
    match t.find? e (ExprMemo.key e) with
    | some b => (b, t)
    | none =>
      let r1 := macM names t ty
      let r := if r1.1 then (true, r1.2) else macM names r1.2 body
      (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))
  | .letE ty val body .. =>
    match t.find? e (ExprMemo.key e) with
    | some b => (b, t)
    | none =>
      let r1 := macM names t ty
      let r2 := if r1.1 then (true, r1.2) else macM names r1.2 val
      let r := if r2.1 then (true, r2.2) else macM names r2.2 body
      (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))
  | .proj s _ sub .. =>
    if names.contains s then (true, t) else
    match t.find? e (ExprMemo.key e) with
    | some b => (b, t)
    | none =>
      let r := macM names t sub
      (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))

theorem macM_spec (names : List Name) :
    ∀ (e : Expr) (t : ExprMemo Bool), t.All (fun x b => b = Expr.mentionsAnyConstP names x) →
      (macM names t e).1 = Expr.mentionsAnyConstP names e ∧
      (macM names t e).2.All (fun x b => b = Expr.mentionsAnyConstP names x) := by
  intro e
  induction e with
  | bvar | sort | lit => intro t ht; exact ⟨by simp [macM, Expr.mentionsAnyConstP], ht⟩
  | const n us => intro t ht; exact ⟨by simp [macM, Expr.mentionsAnyConstP], ht⟩
  | fvar i ty ih =>
    intro t ht
    simp only [macM]
    split
    · rename_i b hb; exact ⟨(ExprMemo.find?_sound ht hb).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := ih t ht
      have hv : (macM names t ty).1 = Expr.mentionsAnyConstP names (.fvar i ty) := by
        rw [h1]; simp [Expr.mentionsAnyConstP]
      exact ⟨hv, ExprMemo.insert_all hv h2⟩
  | app f a ihf iha =>
    intro t ht
    simp only [macM]
    split
    · rename_i b hb; exact ⟨(ExprMemo.find?_sound ht hb).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := ihf t ht
      have key : (if (macM names t f).1 then (true, (macM names t f).2)
          else macM names (macM names t f).2 a).1 = Expr.mentionsAnyConstP names (.app f a) ∧
          (if (macM names t f).1 then (true, (macM names t f).2)
          else macM names (macM names t f).2 a).2.All (fun x b => b = Expr.mentionsAnyConstP names x) := by
        split
        · rename_i hb; refine ⟨?_, h2⟩; simp [Expr.mentionsAnyConstP, ← h1, hb]
        · rename_i hb; obtain ⟨h3, h4⟩ := iha _ h2
          refine ⟨?_, h4⟩; simp [Expr.mentionsAnyConstP, ← h1, hb, h3]
      exact ⟨key.1, ExprMemo.insert_all key.1 key.2⟩
  | lam ty body iht ihb =>
    intro t ht
    simp only [macM]
    split
    · rename_i b hb; exact ⟨(ExprMemo.find?_sound ht hb).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := iht t ht
      have key : (if (macM names t ty).1 then (true, (macM names t ty).2)
          else macM names (macM names t ty).2 body).1 = Expr.mentionsAnyConstP names (.lam ty body) ∧
          (if (macM names t ty).1 then (true, (macM names t ty).2)
          else macM names (macM names t ty).2 body).2.All (fun x b => b = Expr.mentionsAnyConstP names x) := by
        split
        · rename_i hb; refine ⟨?_, h2⟩; simp [Expr.mentionsAnyConstP, ← h1, hb]
        · rename_i hb; obtain ⟨h3, h4⟩ := ihb _ h2
          refine ⟨?_, h4⟩; simp [Expr.mentionsAnyConstP, ← h1, hb, h3]
      exact ⟨key.1, ExprMemo.insert_all key.1 key.2⟩
  | forallE ty body iht ihb =>
    intro t ht
    simp only [macM]
    split
    · rename_i b hb; exact ⟨(ExprMemo.find?_sound ht hb).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := iht t ht
      have key : (if (macM names t ty).1 then (true, (macM names t ty).2)
          else macM names (macM names t ty).2 body).1 = Expr.mentionsAnyConstP names (.forallE ty body) ∧
          (if (macM names t ty).1 then (true, (macM names t ty).2)
          else macM names (macM names t ty).2 body).2.All (fun x b => b = Expr.mentionsAnyConstP names x) := by
        split
        · rename_i hb; refine ⟨?_, h2⟩; simp [Expr.mentionsAnyConstP, ← h1, hb]
        · rename_i hb; obtain ⟨h3, h4⟩ := ihb _ h2
          refine ⟨?_, h4⟩; simp [Expr.mentionsAnyConstP, ← h1, hb, h3]
      exact ⟨key.1, ExprMemo.insert_all key.1 key.2⟩
  | letE ty val body iht ihv ihb =>
    intro t ht
    simp only [macM]
    split
    · rename_i b hb; exact ⟨(ExprMemo.find?_sound ht hb).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := iht t ht
      generalize hr1 : macM names t ty = r1 at *
      have k2 : (if r1.1 then (true, r1.2) else macM names r1.2 val).1 =
            (Expr.mentionsAnyConstP names ty || Expr.mentionsAnyConstP names val) ∧
          (if r1.1 then (true, r1.2) else macM names r1.2 val).2.All
            (fun x b => b = Expr.mentionsAnyConstP names x) := by
        split
        · rename_i hb; exact ⟨by simp [← h1, hb], h2⟩
        · rename_i hb; obtain ⟨h3, h4⟩ := ihv _ h2; exact ⟨by simp [← h1, hb, h3], h4⟩
      generalize hr2 : (if r1.1 then (true, r1.2) else macM names r1.2 val) = r2 at *
      have key : (if r2.1 then (true, r2.2) else macM names r2.2 body).1 =
            Expr.mentionsAnyConstP names (.letE ty val body) ∧
          (if r2.1 then (true, r2.2) else macM names r2.2 body).2.All
            (fun x b => b = Expr.mentionsAnyConstP names x) := by
        split
        · rename_i hb; refine ⟨?_, k2.2⟩; simp [Expr.mentionsAnyConstP, ← k2.1] at hb ⊢; simp [hb]
        · rename_i hb; obtain ⟨h3, h4⟩ := ihb _ k2.2
          refine ⟨?_, h4⟩; simp [Expr.mentionsAnyConstP, ← k2.1] at hb ⊢; simp [hb, h3]
      exact ⟨key.1, ExprMemo.insert_all key.1 key.2⟩
  | proj s i sub ih =>
    intro t ht
    simp only [macM]
    split
    · rename_i hs; simp at hs; exact ⟨by simp [Expr.mentionsAnyConstP, hs], ht⟩
    · rename_i hs
      simp at hs
      split
      · rename_i b hb; exact ⟨(ExprMemo.find?_sound ht hb).symm ▸ rfl, ht⟩
      · obtain ⟨h1, h2⟩ := ih t ht
        have hv : (macM names t sub).1 = Expr.mentionsAnyConstP names (.proj s i sub) := by
          rw [h1]; simp [Expr.mentionsAnyConstP, hs]
        exact ⟨hv, ExprMemo.insert_all hv h2⟩

/-! ## `nestOccP`, memoised -/

/-- `nestOccP names lo hi`, with a memo of the compound nodes' answers. -/
def noM (names : List Name) (lo hi : Nat) (t : ExprMemo Bool) (e : Expr) : Bool × ExprMemo Bool :=
  match e with
  | .bvar .. | .sort .. | .lit .. => (false, t)
  | .const n .. => (names.contains n, t)
  | .fvar i .. => (decide (lo ≤ i ∧ i < hi), t)
  | .app f a .. =>
    match t.find? e (ExprMemo.key e) with
    | some b => (b, t)
    | none =>
      let r1 := noM names lo hi t f
      let r := if r1.1 then (true, r1.2) else noM names lo hi r1.2 a
      (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))
  | .lam ty body .. | .forallE ty body .. =>
    match t.find? e (ExprMemo.key e) with
    | some b => (b, t)
    | none =>
      let r1 := noM names lo hi t ty
      let r := if r1.1 then (true, r1.2) else noM names lo hi r1.2 body
      (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))
  | .letE ty val body .. =>
    match t.find? e (ExprMemo.key e) with
    | some b => (b, t)
    | none =>
      let r1 := noM names lo hi t ty
      let r2 := if r1.1 then (true, r1.2) else noM names lo hi r1.2 val
      let r := if r2.1 then (true, r2.2) else noM names lo hi r2.2 body
      (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))
  | .proj _ _ sub .. =>
    match t.find? e (ExprMemo.key e) with
    | some b => (b, t)
    | none =>
      let r := noM names lo hi t sub
      (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))

theorem noM_spec (names : List Name) (lo hi : Nat) :
    ∀ (e : Expr) (t : ExprMemo Bool), t.All (fun x b => b = Expr.nestOccP names lo hi x) →
      (noM names lo hi t e).1 = Expr.nestOccP names lo hi e ∧
      (noM names lo hi t e).2.All (fun x b => b = Expr.nestOccP names lo hi x) := by
  intro e
  induction e with
  | bvar | sort | lit => intro t ht; exact ⟨by simp [noM, Expr.nestOccP], ht⟩
  | const n us => intro t ht; exact ⟨by simp [noM, Expr.nestOccP], ht⟩
  | fvar i ty ih => intro t ht; exact ⟨by simp [noM, Expr.nestOccP], ht⟩
  | app f a ihf iha =>
    intro t ht
    simp only [noM]
    split
    · rename_i b hb; exact ⟨(ExprMemo.find?_sound ht hb).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := ihf t ht
      have key : (if (noM names lo hi t f).1 then (true, (noM names lo hi t f).2)
          else noM names lo hi (noM names lo hi t f).2 a).1 = Expr.nestOccP names lo hi (.app f a) ∧
          (if (noM names lo hi t f).1 then (true, (noM names lo hi t f).2)
          else noM names lo hi (noM names lo hi t f).2 a).2.All (fun x b => b = Expr.nestOccP names lo hi x) := by
        split
        · rename_i hb; refine ⟨?_, h2⟩; simp [Expr.nestOccP, ← h1, hb]
        · rename_i hb; obtain ⟨h3, h4⟩ := iha _ h2
          refine ⟨?_, h4⟩; simp [Expr.nestOccP, ← h1, hb, h3]
      exact ⟨key.1, ExprMemo.insert_all key.1 key.2⟩
  | lam ty body iht ihb =>
    intro t ht
    simp only [noM]
    split
    · rename_i b hb; exact ⟨(ExprMemo.find?_sound ht hb).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := iht t ht
      have key : (if (noM names lo hi t ty).1 then (true, (noM names lo hi t ty).2)
          else noM names lo hi (noM names lo hi t ty).2 body).1 = Expr.nestOccP names lo hi (.lam ty body) ∧
          (if (noM names lo hi t ty).1 then (true, (noM names lo hi t ty).2)
          else noM names lo hi (noM names lo hi t ty).2 body).2.All (fun x b => b = Expr.nestOccP names lo hi x) := by
        split
        · rename_i hb; refine ⟨?_, h2⟩; simp [Expr.nestOccP, ← h1, hb]
        · rename_i hb; obtain ⟨h3, h4⟩ := ihb _ h2
          refine ⟨?_, h4⟩; simp [Expr.nestOccP, ← h1, hb, h3]
      exact ⟨key.1, ExprMemo.insert_all key.1 key.2⟩
  | forallE ty body iht ihb =>
    intro t ht
    simp only [noM]
    split
    · rename_i b hb; exact ⟨(ExprMemo.find?_sound ht hb).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := iht t ht
      have key : (if (noM names lo hi t ty).1 then (true, (noM names lo hi t ty).2)
          else noM names lo hi (noM names lo hi t ty).2 body).1 = Expr.nestOccP names lo hi (.forallE ty body) ∧
          (if (noM names lo hi t ty).1 then (true, (noM names lo hi t ty).2)
          else noM names lo hi (noM names lo hi t ty).2 body).2.All (fun x b => b = Expr.nestOccP names lo hi x) := by
        split
        · rename_i hb; refine ⟨?_, h2⟩; simp [Expr.nestOccP, ← h1, hb]
        · rename_i hb; obtain ⟨h3, h4⟩ := ihb _ h2
          refine ⟨?_, h4⟩; simp [Expr.nestOccP, ← h1, hb, h3]
      exact ⟨key.1, ExprMemo.insert_all key.1 key.2⟩
  | letE ty val body iht ihv ihb =>
    intro t ht
    simp only [noM]
    split
    · rename_i b hb; exact ⟨(ExprMemo.find?_sound ht hb).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := iht t ht
      generalize hr1 : noM names lo hi t ty = r1 at *
      have k2 : (if r1.1 then (true, r1.2) else noM names lo hi r1.2 val).1 =
            (Expr.nestOccP names lo hi ty || Expr.nestOccP names lo hi val) ∧
          (if r1.1 then (true, r1.2) else noM names lo hi r1.2 val).2.All
            (fun x b => b = Expr.nestOccP names lo hi x) := by
        split
        · rename_i hb; exact ⟨by simp [← h1, hb], h2⟩
        · rename_i hb; obtain ⟨h3, h4⟩ := ihv _ h2; exact ⟨by simp [← h1, hb, h3], h4⟩
      generalize hr2 : (if r1.1 then (true, r1.2) else noM names lo hi r1.2 val) = r2 at *
      have key : (if r2.1 then (true, r2.2) else noM names lo hi r2.2 body).1 =
            Expr.nestOccP names lo hi (.letE ty val body) ∧
          (if r2.1 then (true, r2.2) else noM names lo hi r2.2 body).2.All
            (fun x b => b = Expr.nestOccP names lo hi x) := by
        split
        · rename_i hb; refine ⟨?_, k2.2⟩; simp [Expr.nestOccP, ← k2.1] at hb ⊢; simp [hb]
        · rename_i hb; obtain ⟨h3, h4⟩ := ihb _ k2.2
          refine ⟨?_, h4⟩; simp [Expr.nestOccP, ← k2.1] at hb ⊢; simp [hb, h3]
      exact ⟨key.1, ExprMemo.insert_all key.1 key.2⟩
  | proj s i sub ih =>
    intro t ht
    simp only [noM]
    split
    · rename_i b hb; exact ⟨(ExprMemo.find?_sound ht hb).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := ih t ht
      have hv : (noM names lo hi t sub).1 = Expr.nestOccP names lo hi (.proj s i sub) := by
        rw [h1]; simp [Expr.nestOccP]
      exact ⟨hv, ExprMemo.insert_all hv h2⟩

/-! ## The replacements -/

theorem mentionsAnyConstP_eq_memo (names : List Name) (e : Expr) :
    Expr.mentionsAnyConstP names e = (macM names (.leaf []) e).1 :=
  ((macM_spec names e (.leaf []) (by simp [ExprMemo.All])).1).symm

theorem nestOccP_eq_memo (names : List Name) (lo hi : Nat) (e : Expr) :
    Expr.nestOccP names lo hi e = (noM names lo hi (.leaf []) e).1 :=
  ((noM_spec names lo hi e (.leaf []) (by simp [ExprMemo.All])).1).symm

/-- The memoised walks, as functions of the specifications' arguments. -/
def mentionsAnyConstM (names : List Name) (e : Expr) : Bool := (macM names (.leaf []) e).1
def nestOccM (names : List Name) (lo hi : Nat) (e : Expr) : Bool := (noM names lo hi (.leaf []) e).1

theorem mentionsAnyConstP_eq_M (names : List Name) (e : Expr) :
    Expr.mentionsAnyConstP names e = mentionsAnyConstM names e := mentionsAnyConstP_eq_memo names e
theorem nestOccP_eq_M (names : List Name) (lo hi : Nat) (e : Expr) :
    Expr.nestOccP names lo hi e = nestOccM names lo hi e := nestOccP_eq_memo names lo hi e

end ConPastel.Impl

namespace ConPastel.Leche
cake_datatype (ConPastel.Impl.ExprMemo Bool)
end ConPastel.Leche

cake_replace ConLeche.Expr.mentionsAnyConstP ConPastel.Impl.mentionsAnyConstM ConPastel.Impl.mentionsAnyConstP_eq_M
cake_replace ConLeche.Expr.nestOccP ConPastel.Impl.nestOccM ConPastel.Impl.nestOccP_eq_M

namespace ConPastel.Impl
open ConLeche

/-! ## `replaceAppsP`, memoised -/

def raM (f : Name → List Level → Option Expr) (b n : Nat) (t : ExprMemo Expr) (e : Expr) :
    Expr × ExprMemo Expr :=
  match e with
  | .bvar .. | .fvar .. | .sort .. | .lit .. => (e, t)
  | .const c us .. => ((Expr.constHoleAt? f n c us).getD e, t)
  | .app a x .. =>
    match t.find? e (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      match Expr.appHoleAt? f b n a x with
      | some r => (r, ExprMemo.insert e r 16 t (ExprMemo.key e))
      | none =>
        let r1 := raM f b n t a
        let r2 := raM f b n r1.2 x
        let r := Expr.mkApp r1.1 r2.1
        (r, ExprMemo.insert e r 16 r2.2 (ExprMemo.key e))
  | .lam ty body .. =>
    match t.find? e (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := raM f b n t ty
      let r2 := raM f b n r1.2 body
      let r := Expr.mkLam r1.1 r2.1
      (r, ExprMemo.insert e r 16 r2.2 (ExprMemo.key e))
  | .forallE ty body .. =>
    match t.find? e (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := raM f b n t ty
      let r2 := raM f b n r1.2 body
      let r := Expr.mkForallE r1.1 r2.1
      (r, ExprMemo.insert e r 16 r2.2 (ExprMemo.key e))
  | .letE ty val body .. =>
    match t.find? e (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := raM f b n t ty
      let r2 := raM f b n r1.2 val
      let r3 := raM f b n r2.2 body
      let r := Expr.mkLetE r1.1 r2.1 r3.1
      (r, ExprMemo.insert e r 16 r3.2 (ExprMemo.key e))
  | .proj sn i sub .. =>
    match t.find? e (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := raM f b n t sub
      let r := Expr.mkProj sn i r1.1
      (r, ExprMemo.insert e r 16 r1.2 (ExprMemo.key e))

theorem raM_spec (f : Name → List Level → Option Expr) (b n : Nat) :
    ∀ (e : Expr) (t : ExprMemo Expr), t.All (fun x r => r = Expr.replaceAppsP f b n x) →
      (raM f b n t e).1 = Expr.replaceAppsP f b n e ∧
      (raM f b n t e).2.All (fun x r => r = Expr.replaceAppsP f b n x) := by
  intro e
  induction e with
  | bvar | fvar | sort | lit => intro t ht; exact ⟨by simp [raM, Expr.replaceAppsP], ht⟩
  | const c us => intro t ht; exact ⟨by simp [raM, Expr.replaceAppsP], ht⟩
  | app a x iha ihx =>
    intro t ht
    simp only [raM]
    split
    · rename_i r hr; exact ⟨(ExprMemo.find?_sound ht hr).symm ▸ rfl, ht⟩
    · split
      · rename_i r hr
        have hv : r = Expr.replaceAppsP f b n (.app a x) := by simp [Expr.replaceAppsP, hr]
        exact ⟨hv, ExprMemo.insert_all (P := fun x r => r = Expr.replaceAppsP f b n x) hv ht⟩
      · rename_i hr
        obtain ⟨h1, h2⟩ := iha t ht
        obtain ⟨h3, h4⟩ := ihx _ h2
        have hv : Expr.mkApp (raM f b n t a).1 (raM f b n (raM f b n t a).2 x).1 =
            Expr.replaceAppsP f b n (.app a x) := by simp [Expr.replaceAppsP, hr, h1, h3]
        exact ⟨hv, ExprMemo.insert_all (P := fun x r => r = Expr.replaceAppsP f b n x) hv h4⟩
  | lam ty body iht ihb =>
    intro t ht
    simp only [raM]
    split
    · rename_i r hr; exact ⟨(ExprMemo.find?_sound ht hr).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := iht t ht
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : Expr.mkLam (raM f b n t ty).1 (raM f b n (raM f b n t ty).2 body).1 =
          Expr.replaceAppsP f b n (.lam ty body) := by simp [Expr.replaceAppsP, h1, h3]
      exact ⟨hv, ExprMemo.insert_all (P := fun x r => r = Expr.replaceAppsP f b n x) hv h4⟩
  | forallE ty body iht ihb =>
    intro t ht
    simp only [raM]
    split
    · rename_i r hr; exact ⟨(ExprMemo.find?_sound ht hr).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := iht t ht
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : Expr.mkForallE (raM f b n t ty).1 (raM f b n (raM f b n t ty).2 body).1 =
          Expr.replaceAppsP f b n (.forallE ty body) := by simp [Expr.replaceAppsP, h1, h3]
      exact ⟨hv, ExprMemo.insert_all (P := fun x r => r = Expr.replaceAppsP f b n x) hv h4⟩
  | letE ty val body iht ihv ihb =>
    intro t ht
    simp only [raM]
    split
    · rename_i r hr; exact ⟨(ExprMemo.find?_sound ht hr).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := iht t ht
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      refine ⟨by simp [Expr.replaceAppsP, h1, h3, h5], ExprMemo.insert_all (P := fun x r => r = Expr.replaceAppsP f b n x) ?_ h6⟩
      simp [Expr.replaceAppsP, h1, h3, h5]
  | proj sn i sub ih =>
    intro t ht
    simp only [raM]
    split
    · rename_i r hr; exact ⟨(ExprMemo.find?_sound ht hr).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := ih t ht
      refine ⟨by simp [Expr.replaceAppsP, h1], ExprMemo.insert_all (P := fun x r => r = Expr.replaceAppsP f b n x) ?_ h2⟩
      simp [Expr.replaceAppsP, h1]

/-! ## `constsResolveFP`, memoised -/

/-- The literal case of `constsResolveFP` (spelled out: `constsResolveFP` itself
is replaced by `constsResolveM`). -/
def crLit (fe : FEnv) : Literal → Bool
  | .natVal _ =>
    (fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
      (fe.find? natSuccName).isSome
  | .strVal _ =>
    (fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
      (fe.find? natSuccName).isSome && (fe.find? stringName).isSome &&
      (fe.find? stringOfListName).isSome &&
      (fe.find? listName).isSome && (fe.find? listNilName).isSome &&
      (fe.find? listConsName).isSome && (fe.find? charName).isSome &&
      (fe.find? charOfNatName).isSome

def crM (fe : FEnv) (t : ExprMemo Bool) (e : Expr) : Bool × ExprMemo Bool :=
  match e with
  | .bvar .. | .sort .. => (true, t)
  | .lit l .. => (crLit fe l, t)
  | .const nm .. => ((fe.find? nm).isSome, t)
  | .fvar _ ty .. =>
    match t.find? e (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r := crM fe t ty
      (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))
  | .app a x .. =>
    match t.find? e (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := crM fe t a
      let r := if r1.1 then crM fe r1.2 x else (false, r1.2)
      (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))
  | .lam ty body .. | .forallE ty body .. =>
    match t.find? e (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := crM fe t ty
      let r := if r1.1 then crM fe r1.2 body else (false, r1.2)
      (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))
  | .letE ty val body .. =>
    match t.find? e (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := crM fe t ty
      let r2 := if r1.1 then crM fe r1.2 val else (false, r1.2)
      let r := if r2.1 then crM fe r2.2 body else (false, r2.2)
      (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))
  | .proj sn _ sub .. =>
    if (fe.find? sn).isSome then
      match t.find? e (ExprMemo.key e) with
      | some r => (r, t)
      | none =>
        let r := crM fe t sub
        (r.1, ExprMemo.insert e r.1 16 r.2 (ExprMemo.key e))
    else (false, t)

theorem crM_spec (fe : FEnv) :
    ∀ (e : Expr) (t : ExprMemo Bool), t.All (fun x r => r = Cached.constsResolveFP fe x) →
      (crM fe t e).1 = Cached.constsResolveFP fe e ∧
      (crM fe t e).2.All (fun x r => r = Cached.constsResolveFP fe x) := by
  intro e
  induction e with
  | bvar | sort | const => intro t ht; exact ⟨by simp [crM, Cached.constsResolveFP], ht⟩
  | lit l => intro t ht; exact ⟨by cases l <;> simp [crM, crLit, Cached.constsResolveFP], ht⟩
  | fvar i ty ih =>
    intro t ht
    simp only [crM]
    split
    · rename_i r hr; exact ⟨(ExprMemo.find?_sound ht hr).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := ih t ht
      have hv : (crM fe t ty).1 = Cached.constsResolveFP fe (.fvar i ty) := by
        rw [h1]; simp [Cached.constsResolveFP]
      exact ⟨hv, ExprMemo.insert_all hv h2⟩
  | app a x iha ihx =>
    intro t ht
    simp only [crM]
    split
    · rename_i r hr; exact ⟨(ExprMemo.find?_sound ht hr).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := iha t ht
      have key : (if (crM fe t a).1 then crM fe (crM fe t a).2 x else (false, (crM fe t a).2)).1 =
            Cached.constsResolveFP fe (.app a x) ∧
          (if (crM fe t a).1 then crM fe (crM fe t a).2 x else (false, (crM fe t a).2)).2.All
            (fun x r => r = Cached.constsResolveFP fe x) := by
        split
        · rename_i hb; obtain ⟨h3, h4⟩ := ihx _ h2
          exact ⟨by simp [Cached.constsResolveFP, ← h1, hb, h3], h4⟩
        · rename_i hb; exact ⟨by simp [Cached.constsResolveFP, ← h1, hb], h2⟩
      exact ⟨key.1, ExprMemo.insert_all key.1 key.2⟩
  | lam ty body iht ihb =>
    intro t ht
    simp only [crM]
    split
    · rename_i r hr; exact ⟨(ExprMemo.find?_sound ht hr).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := iht t ht
      have key : (if (crM fe t ty).1 then crM fe (crM fe t ty).2 body else (false, (crM fe t ty).2)).1 =
            Cached.constsResolveFP fe (.lam ty body) ∧
          (if (crM fe t ty).1 then crM fe (crM fe t ty).2 body else (false, (crM fe t ty).2)).2.All
            (fun x r => r = Cached.constsResolveFP fe x) := by
        split
        · rename_i hb; obtain ⟨h3, h4⟩ := ihb _ h2
          exact ⟨by simp [Cached.constsResolveFP, ← h1, hb, h3], h4⟩
        · rename_i hb; exact ⟨by simp [Cached.constsResolveFP, ← h1, hb], h2⟩
      exact ⟨key.1, ExprMemo.insert_all key.1 key.2⟩
  | forallE ty body iht ihb =>
    intro t ht
    simp only [crM]
    split
    · rename_i r hr; exact ⟨(ExprMemo.find?_sound ht hr).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := iht t ht
      have key : (if (crM fe t ty).1 then crM fe (crM fe t ty).2 body else (false, (crM fe t ty).2)).1 =
            Cached.constsResolveFP fe (.forallE ty body) ∧
          (if (crM fe t ty).1 then crM fe (crM fe t ty).2 body else (false, (crM fe t ty).2)).2.All
            (fun x r => r = Cached.constsResolveFP fe x) := by
        split
        · rename_i hb; obtain ⟨h3, h4⟩ := ihb _ h2
          exact ⟨by simp [Cached.constsResolveFP, ← h1, hb, h3], h4⟩
        · rename_i hb; exact ⟨by simp [Cached.constsResolveFP, ← h1, hb], h2⟩
      exact ⟨key.1, ExprMemo.insert_all key.1 key.2⟩
  | letE ty val body iht ihv ihb =>
    intro t ht
    simp only [crM]
    split
    · rename_i r hr; exact ⟨(ExprMemo.find?_sound ht hr).symm ▸ rfl, ht⟩
    · obtain ⟨h1, h2⟩ := iht t ht
      generalize hr1 : crM fe t ty = r1 at *
      have k2 : (if r1.1 then crM fe r1.2 val else (false, r1.2)).1 =
            (Cached.constsResolveFP fe ty && Cached.constsResolveFP fe val) ∧
          (if r1.1 then crM fe r1.2 val else (false, r1.2)).2.All
            (fun x r => r = Cached.constsResolveFP fe x) := by
        split
        · rename_i hb; obtain ⟨h3, h4⟩ := ihv _ h2; exact ⟨by simp [← h1, hb, h3], h4⟩
        · rename_i hb; exact ⟨by simp [← h1, hb], h2⟩
      generalize hr2 : (if r1.1 then crM fe r1.2 val else (false, r1.2)) = r2 at *
      have key : (if r2.1 then crM fe r2.2 body else (false, r2.2)).1 =
            Cached.constsResolveFP fe (.letE ty val body) ∧
          (if r2.1 then crM fe r2.2 body else (false, r2.2)).2.All
            (fun x r => r = Cached.constsResolveFP fe x) := by
        split
        · rename_i hb; obtain ⟨h3, h4⟩ := ihb _ k2.2
          refine ⟨?_, h4⟩; simp [Cached.constsResolveFP, ← k2.1] at hb ⊢; simp [hb, h3]
        · rename_i hb; refine ⟨?_, k2.2⟩; simp [Cached.constsResolveFP, ← k2.1] at hb ⊢
          intro h; simp [hb] at h
      exact ⟨key.1, ExprMemo.insert_all key.1 key.2⟩
  | proj sn i sub ih =>
    intro t ht
    simp only [crM]
    split
    · rename_i hs
      split
      · rename_i r hr; exact ⟨(ExprMemo.find?_sound ht hr).symm ▸ rfl, ht⟩
      · obtain ⟨h1, h2⟩ := ih t ht
        have hv : (crM fe t sub).1 = Cached.constsResolveFP fe (.proj sn i sub) := by
          rw [h1]; simp [Cached.constsResolveFP, hs]
        exact ⟨hv, ExprMemo.insert_all hv h2⟩
    · rename_i hs; exact ⟨by simp [Cached.constsResolveFP, hs], ht⟩

def replaceAppsM (f : Name → List Level → Option Expr) (b n : Nat) (e : Expr) : Expr :=
  (raM f b n (.leaf []) e).1
def constsResolveM (fe : FEnv) (e : Expr) : Bool := (crM fe (.leaf []) e).1

theorem replaceAppsP_eq_M (f : Name → List Level → Option Expr) (b n : Nat) (e : Expr) :
    Expr.replaceAppsP f b n e = replaceAppsM f b n e :=
  ((raM_spec f b n e (.leaf []) (by simp [ExprMemo.All])).1).symm
theorem constsResolveFP_eq_M (fe : FEnv) (e : Expr) :
    Cached.constsResolveFP fe e = constsResolveM fe e :=
  ((crM_spec fe e (.leaf []) (by simp [ExprMemo.All])).1).symm

end ConPastel.Impl

namespace ConPastel.Leche
cake_datatype (Option (ConLeche.Name × List ConLeche.Level))
cake_datatype (ConPastel.Impl.ExprMemo ConLeche.Expr)
end ConPastel.Leche

cake_replace ConLeche.Expr.replaceAppsP ConPastel.Impl.replaceAppsM ConPastel.Impl.replaceAppsP_eq_M
cake_replace ConLeche.Cached.constsResolveFP ConPastel.Impl.constsResolveM ConPastel.Impl.constsResolveFP_eq_M

namespace ConPastel.Impl
open ConLeche

/-! ## A generic sharing-preserving replace walk -/

/-- The generic replace: below the cut-off `cut`, leaves by `leaf`, free
variables by `lf` (`none`: descend into the type), the rest rebuilt, the
cursor bumped by `bump` under binders. -/
def rwP (cut : Expr → Nat → Bool) (leaf : Expr → Nat → Expr)
    (lf : Expr → Nat → Expr → Nat → Option Expr) (bump : Nat → Nat) (e : Expr) (c : Nat) : Expr :=
  if cut e c then e else
  match e with
  | .bvar .. | .sort .. | .const .. | .lit .. => leaf e c
  | .fvar idx ty .. =>
    match lf e idx ty c with
    | some r => r
    | none => Expr.mkFVar idx (rwP cut leaf lf bump ty c)
  | .app f a .. => Expr.mkApp (rwP cut leaf lf bump f c) (rwP cut leaf lf bump a c)
  | .lam ty b .. => Expr.mkLam (rwP cut leaf lf bump ty c) (rwP cut leaf lf bump b (bump c))
  | .forallE ty b .. => Expr.mkForallE (rwP cut leaf lf bump ty c) (rwP cut leaf lf bump b (bump c))
  | .letE ty v b .. =>
    Expr.mkLetE (rwP cut leaf lf bump ty c) (rwP cut leaf lf bump v c) (rwP cut leaf lf bump b (bump c))
  | .proj sn i x .. => Expr.mkProj sn i (rwP cut leaf lf bump x c)

/-- Memo entries `(node, cursor, result)`. -/
abbrev RMemo := ExprMemo (Nat × Expr)

def findC (e : Expr) (c : Nat) : List (Expr × Nat × Expr) → Option Expr
  | [] => none
  | (x, c', r) :: t => if c' == c && exprEqD x e then some r else findC e c t

def RMemo.find? (e : Expr) (c : Nat) : RMemo → Nat → Option Expr
  | .leaf l, _ => findC e c l
  | .node a b, k => if k % 2 = 0 then RMemo.find? e c a (k / 2) else RMemo.find? e c b (k / 2)

theorem findC_sound {P : Expr → Nat × Expr → Prop} {e : Expr} {c : Nat} :
    ∀ {l : List (Expr × Nat × Expr)} {r : Expr}, (∀ p ∈ l, P p.1 p.2) → findC e c l = some r → P e (c, r)
  | [], _, _, h => by simp [findC] at h
  | (x, c', w) :: t, r, hl, h => by
    simp only [findC] at h
    split at h
    · rename_i hx; cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      obtain ⟨hc, he⟩ := hx
      have := (exprEqD_iff x e).mp he; subst this; subst hc
      exact hl (x, c', _) (by simp)
    · exact findC_sound (fun p hp => hl p (by simp [hp])) h

theorem RMemo.find?_sound {P : Expr → Nat × Expr → Prop} {e : Expr} {c : Nat} :
    ∀ {t : RMemo} {k : Nat} {r : Expr}, t.All P → RMemo.find? e c t k = some r → P e (c, r)
  | .leaf l, _, _, ht, h => findC_sound ht h
  | .node a b, k, r, ht, h => by
    simp only [RMemo.find?] at h
    split at h
    · exact RMemo.find?_sound ht.1 h
    · exact RMemo.find?_sound ht.2 h

/-- `rwP`, memoised on (node, cursor) for the compound nodes. -/
def rwM (cut : Expr → Nat → Bool) (leaf : Expr → Nat → Expr)
    (lf : Expr → Nat → Expr → Nat → Option Expr) (bump : Nat → Nat)
    (t : RMemo) (e : Expr) (c : Nat) : Expr × RMemo :=
  if cut e c then (e, t) else
  match e with
  | .bvar .. | .sort .. | .const .. | .lit .. => (leaf e c, t)
  | .fvar idx ty .. =>
    match lf e idx ty c with
    | some r => (r, t)
    | none =>
      match RMemo.find? e c t (ExprMemo.key e) with
      | some r => (r, t)
      | none =>
        let r1 := rwM cut leaf lf bump t ty c
        let r := Expr.mkFVar idx r1.1
        (r, ExprMemo.insert e (c, r) 16 r1.2 (ExprMemo.key e))
  | .app f a .. =>
    match RMemo.find? e c t (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := rwM cut leaf lf bump t f c
      let r2 := rwM cut leaf lf bump r1.2 a c
      let r := Expr.mkApp r1.1 r2.1
      (r, ExprMemo.insert e (c, r) 16 r2.2 (ExprMemo.key e))
  | .lam ty b .. =>
    match RMemo.find? e c t (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := rwM cut leaf lf bump t ty c
      let r2 := rwM cut leaf lf bump r1.2 b (bump c)
      let r := Expr.mkLam r1.1 r2.1
      (r, ExprMemo.insert e (c, r) 16 r2.2 (ExprMemo.key e))
  | .forallE ty b .. =>
    match RMemo.find? e c t (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := rwM cut leaf lf bump t ty c
      let r2 := rwM cut leaf lf bump r1.2 b (bump c)
      let r := Expr.mkForallE r1.1 r2.1
      (r, ExprMemo.insert e (c, r) 16 r2.2 (ExprMemo.key e))
  | .letE ty v b .. =>
    match RMemo.find? e c t (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := rwM cut leaf lf bump t ty c
      let r2 := rwM cut leaf lf bump r1.2 v c
      let r3 := rwM cut leaf lf bump r2.2 b (bump c)
      let r := Expr.mkLetE r1.1 r2.1 r3.1
      (r, ExprMemo.insert e (c, r) 16 r3.2 (ExprMemo.key e))
  | .proj sn i x .. =>
    match RMemo.find? e c t (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := rwM cut leaf lf bump t x c
      let r := Expr.mkProj sn i r1.1
      (r, ExprMemo.insert e (c, r) 16 r1.2 (ExprMemo.key e))

section
variable (cut : Expr → Nat → Bool) (leaf : Expr → Nat → Expr)
    (lf : Expr → Nat → Expr → Nat → Option Expr) (bump : Nat → Nat)

/-- The memo invariant: every entry is the plain walk's result. -/
abbrev RGood (t : RMemo) : Prop :=
  t.All (fun x p => p.2 = rwP cut leaf lf bump x p.1)

theorem rwM_spec : ∀ (e : Expr) (c : Nat) (t : RMemo), RGood cut leaf lf bump t →
    (rwM cut leaf lf bump t e c).1 = rwP cut leaf lf bump e c ∧
    RGood cut leaf lf bump (rwM cut leaf lf bump t e c).2 := by
  intro e
  induction e with
  | bvar | sort | const | lit =>
    intro c t ht; rw [rwM]
    split
    · rename_i hcut; exact ⟨by rw [rwP]; simp [hcut], ht⟩
    · rename_i hcut; exact ⟨by rw [rwP]; simp [hcut], ht⟩
  | fvar idx ty ih =>
    intro c t ht; rw [rwM]
    split
    · rename_i hcut; exact ⟨by rw [rwP]; simp [hcut], ht⟩
    · rename_i hcut
      split
      · rename_i r hlf; exact ⟨by rw [rwP]; simp [hcut, hlf], ht⟩
      · rename_i hlf
        split
        · rename_i r hr; exact ⟨RMemo.find?_sound (P := fun x p => p.2 = rwP cut leaf lf bump x p.1) ht hr, ht⟩
        · obtain ⟨h1, h2⟩ := ih c t ht
          refine ⟨?_, ExprMemo.insert_all ?_ h2⟩ <;> (dsimp only; rw [rwP]; simp [hcut, hlf, h1])
  | app f a ihf iha =>
    intro c t ht; rw [rwM]
    split
    · rename_i hcut; exact ⟨by rw [rwP]; simp [hcut], ht⟩
    · rename_i hcut
      split
      · rename_i r hr; exact ⟨RMemo.find?_sound (P := fun x p => p.2 = rwP cut leaf lf bump x p.1) ht hr, ht⟩
      · obtain ⟨h1, h2⟩ := ihf c t ht
        obtain ⟨h3, h4⟩ := iha c _ h2
        refine ⟨?_, ExprMemo.insert_all ?_ h4⟩ <;> (dsimp only; rw [rwP]; simp [hcut, h1, h3])
  | lam ty b iht ihb =>
    intro c t ht; rw [rwM]
    split
    · rename_i hcut; exact ⟨by rw [rwP]; simp [hcut], ht⟩
    · rename_i hcut
      split
      · rename_i r hr; exact ⟨RMemo.find?_sound (P := fun x p => p.2 = rwP cut leaf lf bump x p.1) ht hr, ht⟩
      · obtain ⟨h1, h2⟩ := iht c t ht
        obtain ⟨h3, h4⟩ := ihb (bump c) _ h2
        refine ⟨?_, ExprMemo.insert_all ?_ h4⟩ <;> (dsimp only; rw [rwP]; simp [hcut, h1, h3])
  | forallE ty b iht ihb =>
    intro c t ht; rw [rwM]
    split
    · rename_i hcut; exact ⟨by rw [rwP]; simp [hcut], ht⟩
    · rename_i hcut
      split
      · rename_i r hr; exact ⟨RMemo.find?_sound (P := fun x p => p.2 = rwP cut leaf lf bump x p.1) ht hr, ht⟩
      · obtain ⟨h1, h2⟩ := iht c t ht
        obtain ⟨h3, h4⟩ := ihb (bump c) _ h2
        refine ⟨?_, ExprMemo.insert_all ?_ h4⟩ <;> (dsimp only; rw [rwP]; simp [hcut, h1, h3])
  | letE ty v b iht ihv ihb =>
    intro c t ht; rw [rwM]
    split
    · rename_i hcut; exact ⟨by rw [rwP]; simp [hcut], ht⟩
    · rename_i hcut
      split
      · rename_i r hr; exact ⟨RMemo.find?_sound (P := fun x p => p.2 = rwP cut leaf lf bump x p.1) ht hr, ht⟩
      · obtain ⟨h1, h2⟩ := iht c t ht
        obtain ⟨h3, h4⟩ := ihv c _ h2
        obtain ⟨h5, h6⟩ := ihb (bump c) _ h4
        refine ⟨?_, ExprMemo.insert_all ?_ h6⟩ <;> (dsimp only; rw [rwP]; simp [hcut, h1, h3, h5])
  | proj sn i x ih =>
    intro c t ht; rw [rwM]
    split
    · rename_i hcut; exact ⟨by rw [rwP]; simp [hcut], ht⟩
    · rename_i hcut
      split
      · rename_i r hr; exact ⟨RMemo.find?_sound (P := fun x p => p.2 = rwP cut leaf lf bump x p.1) ht hr, ht⟩
      · obtain ⟨h1, h2⟩ := ih c t ht
        refine ⟨?_, ExprMemo.insert_all ?_ h2⟩ <;> (dsimp only; rw [rwP]; simp [hcut, h1])

theorem rwM_eq (e : Expr) (c : Nat) :
    (rwM cut leaf lf bump (.leaf []) e c).1 = rwP cut leaf lf bump e c :=
  (rwM_spec cut leaf lf bump e c (.leaf []) (by simp [ExprMemo.All])).1
end

/-! ## The substitution walks as instances -/

def liftLeaf (amount : Nat) (e : Expr) (c : Nat) : Expr :=
  match e with
  | .bvar i .. => if i ≥ c then Expr.mkBvar (i + amount) else e
  | _ => e
def inst1Leaf (v : Expr) (e : Expr) (d : Nat) : Expr :=
  match e with
  | .bvar i .. => if i = d then v else if i > d then Expr.mkBvar (i - 1) else e
  | _ => e
def instLiftLeaf (vs : Array Expr) (e : Expr) (d : Nat) : Expr :=
  match e with
  | .bvar i .. =>
    if i < d then e
    else if h : i - d < vs.size then Expr.liftLooseBVarsP d vs[i - d] 0
    else Expr.mkBvar (i - vs.size)
  | _ => e
def ilpLeaf (ks : List Name) (us : List Level) (e : Expr) (_ : Nat) : Expr :=
  match e with
  | .sort u .. => Expr.mkSort (Level.subst ks us u)
  | .const n vs .. => Expr.mkConst n (vs.map (Level.subst ks us))
  | _ => e
def taLeaf (names : List Name) (lvls : List Level) (holes : List Expr) (e : Expr) (_ : Nat) : Expr :=
  match e with
  | .const n us .. => Expr.targetAbsConst names lvls holes n us
  | _ => e

theorem liftLooseBVarsP_rw (amount : Nat) (e : Expr) (c : Nat) :
    Expr.liftLooseBVarsP amount e c =
      rwP (fun e c => decide (e.bvarB ≤ c)) (liftLeaf amount) (fun e _ _ _ => some e) Nat.succ e c := by
  induction e generalizing c <;> (rw [Expr.liftLooseBVarsP, rwP]; simp_all [liftLeaf])

theorem instantiate1P_rw (v e : Expr) (d : Nat) :
    Expr.instantiate1P v e d =
      rwP (fun e c => decide (e.bvarB ≤ c)) (inst1Leaf v) (fun e _ _ _ => some e) Nat.succ e d := by
  induction e generalizing d <;> (rw [Expr.instantiate1P, rwP]; simp_all [inst1Leaf])

theorem instantiateLiftP_rw (vs : Array Expr) (e : Expr) (d : Nat) :
    Expr.instantiateLiftP vs e d =
      rwP (fun e c => decide (e.bvarB ≤ c)) (instLiftLeaf vs) (fun e _ _ _ => some e) Nat.succ e d := by
  induction e generalizing d <;> (rw [Expr.instantiateLiftP, rwP]; simp_all [instLiftLeaf])

theorem abstract1P_rw (d : Nat) (e : Expr) (k : Nat) :
    Expr.abstract1P d e k =
      rwP (fun e _ => decide (e.fvarB ≤ d)) (fun e _ => e)
        (fun e idx _ k => some (if idx = d then Expr.mkBvar k else e)) Nat.succ e k := by
  induction e generalizing k <;> (rw [Expr.abstract1P, rwP]; simp_all)

theorem abstractRangeP_rw (d k : Nat) (e : Expr) (c : Nat) :
    Expr.abstractRangeP d k e c =
      rwP (fun e _ => decide (e.fvarB ≤ d)) (fun e _ => e)
        (fun e idx _ c => some (if d ≤ idx ∧ idx < d + k then Expr.mkBvar (c + (d + k - 1 - idx)) else e))
        Nat.succ e c := by
  induction e generalizing c <;> (rw [Expr.abstractRangeP, rwP]; simp_all)

theorem replaceFVarsP_rw (f : Nat → Option Expr) (e : Expr) :
    Expr.replaceFVarsP f e =
      rwP (fun e _ => e.fvarB == 0) (fun e _ => e)
        (fun _ idx ty _ => some ((f idx).getD (.fvar idx ty))) id e 0 := by
  induction e <;> (rw [Expr.replaceFVarsP, rwP]; simp_all)

theorem instLevelParamsP_rw (ks : List Name) (us : List Level) (e : Expr) :
    Expr.instLevelParamsP ks us e =
      rwP (fun e _ => !e.hasLP) (ilpLeaf ks us) (fun _ _ _ _ => none) id e 0 := by
  induction e <;> (rw [Expr.instLevelParamsP, rwP]; simp_all [ilpLeaf])

theorem targetAbsP_rw (names : List Name) (lvls : List Level) (holes : List Expr) (e : Expr) :
    Expr.targetAbsP names lvls holes e =
      rwP (fun _ _ => false) (taLeaf names lvls holes) (fun e _ _ _ => some e) id e 0 := by
  induction e <;> (rw [Expr.targetAbsP, rwP]; simp_all [taLeaf])


/-! ## The memoised substitution walks (the replacements) -/

def liftLooseBVarsM (amount : Nat) (e : Expr) (c : Nat) : Expr :=
  (rwM (fun e c => decide (e.bvarB ≤ c)) (liftLeaf amount) (fun e _ _ _ => some e) Nat.succ (.leaf []) e c).1
def instantiate1M (v e : Expr) (d : Nat) : Expr :=
  (rwM (fun e c => decide (e.bvarB ≤ c)) (inst1Leaf v) (fun e _ _ _ => some e) Nat.succ (.leaf []) e d).1
def instantiateLiftM (vs : Array Expr) (e : Expr) (d : Nat) : Expr :=
  (rwM (fun e c => decide (e.bvarB ≤ c)) (instLiftLeaf vs) (fun e _ _ _ => some e) Nat.succ (.leaf []) e d).1
def abstract1M (d : Nat) (e : Expr) (k : Nat) : Expr :=
  (rwM (fun e _ => decide (e.fvarB ≤ d)) (fun e _ => e)
    (fun e idx _ k => some (if idx = d then Expr.mkBvar k else e)) Nat.succ (.leaf []) e k).1
def abstractRangeM (d k : Nat) (e : Expr) (c : Nat) : Expr :=
  (rwM (fun e _ => decide (e.fvarB ≤ d)) (fun e _ => e)
    (fun e idx _ c => some (if d ≤ idx ∧ idx < d + k then Expr.mkBvar (c + (d + k - 1 - idx)) else e))
    Nat.succ (.leaf []) e c).1
def replaceFVarsM (f : Nat → Option Expr) (e : Expr) : Expr :=
  (rwM (fun e _ => e.fvarB == 0) (fun e _ => e)
    (fun _ idx ty _ => some ((f idx).getD (.fvar idx ty))) id (.leaf []) e 0).1
def instLevelParamsM (ks : List Name) (us : List Level) (e : Expr) : Expr :=
  (rwM (fun e _ => !e.hasLP) (ilpLeaf ks us) (fun _ _ _ _ => none) id (.leaf []) e 0).1
def targetAbsM (names : List Name) (lvls : List Level) (holes : List Expr) (e : Expr) : Expr :=
  (rwM (fun _ _ => false) (taLeaf names lvls holes) (fun e _ _ _ => some e) id (.leaf []) e 0).1

theorem liftLooseBVarsP_eq_M (amount : Nat) (e : Expr) (c : Nat) :
    Expr.liftLooseBVarsP amount e c = liftLooseBVarsM amount e c := by
  rw [liftLooseBVarsP_rw, liftLooseBVarsM, rwM_eq]
theorem instantiate1P_eq_M (v e : Expr) (d : Nat) :
    Expr.instantiate1P v e d = instantiate1M v e d := by
  rw [instantiate1P_rw, instantiate1M, rwM_eq]
theorem instantiateLiftP_eq_M (vs : Array Expr) (e : Expr) (d : Nat) :
    Expr.instantiateLiftP vs e d = instantiateLiftM vs e d := by
  rw [instantiateLiftP_rw, instantiateLiftM, rwM_eq]
theorem abstract1P_eq_M (d : Nat) (e : Expr) (k : Nat) :
    Expr.abstract1P d e k = abstract1M d e k := by
  rw [abstract1P_rw, abstract1M, rwM_eq]
theorem abstractRangeP_eq_M (d k : Nat) (e : Expr) (c : Nat) :
    Expr.abstractRangeP d k e c = abstractRangeM d k e c := by
  rw [abstractRangeP_rw, abstractRangeM, rwM_eq]
theorem replaceFVarsP_eq_M (f : Nat → Option Expr) (e : Expr) :
    Expr.replaceFVarsP f e = replaceFVarsM f e := by
  rw [replaceFVarsP_rw, replaceFVarsM, rwM_eq]
theorem instLevelParamsP_eq_M (ks : List Name) (us : List Level) (e : Expr) :
    Expr.instLevelParamsP ks us e = instLevelParamsM ks us e := by
  rw [instLevelParamsP_rw, instLevelParamsM, rwM_eq]
theorem targetAbsP_eq_M (names : List Name) (lvls : List Level) (holes : List Expr) (e : Expr) :
    Expr.targetAbsP names lvls holes e = targetAbsM names lvls holes e := by
  rw [targetAbsP_rw, targetAbsM, rwM_eq]

/-- A copy of `Expr.instantiateListP` that `cake_replace` leaves alone (the memoised
walk's leaf re-enters it). -/
def instListPl (vs : Array Expr) (e : Expr) (k : Nat) (d : Nat) : Expr :=
  if k = 0 then e
  else if e.bvarB ≤ d then e
  else
    match e with
    | .bvar i .. =>
      if i < d then e
      else if _h : i - d < k then
        if h : i - d < vs.size then
          let w := vs[i - d]
          if i - d = 0 || w.bvarB ≤ d then w
          else instListPl vs w (i - d) d
        else e
      else Expr.mkBvar (i - k)
    | .fvar .. | .sort .. | .const .. | .lit .. => e
    | .app f a .. => Expr.mkApp (instListPl vs f k d) (instListPl vs a k d)
    | .lam ty body .. => Expr.mkLam (instListPl vs ty k d) (instListPl vs body k (d + 1))
    | .forallE ty body .. =>
      Expr.mkForallE (instListPl vs ty k d) (instListPl vs body k (d + 1))
    | .letE ty val body .. =>
      Expr.mkLetE (instListPl vs ty k d) (instListPl vs val k d) (instListPl vs body k (d + 1))
    | .proj sn i sub .. => Expr.mkProj sn i (instListPl vs sub k d)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

theorem instListPl_eq (vs : Array Expr) : ∀ (k : Nat) (e : Expr) (d : Nat),
    instListPl vs e k d = Expr.instantiateListP vs e k d := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
    intro e
    induction e with
    | bvar i =>
      intro d; rw [instListPl, Expr.instantiateListP]
      by_cases hk : k = 0
      · simp [hk]
      · simp only [hk, if_false]
        split <;> try rfl
        split <;> try rfl
        split
        · rename_i hlt; split <;> try rfl
          split <;> try rfl
          exact ihk _ hlt _ _
        · rfl
    | _ => intro d; rw [instListPl, Expr.instantiateListP] <;> simp_all

/-- A copy of `Expr.instantiateRevP` that `cake_replace` leaves alone (the memoised
walk's leaf re-enters it). -/
def instRevPl (vs : Array Expr) (e : Expr) (k : Nat) (d : Nat) : Expr :=
  if k = 0 then e
  else if e.bvarB ≤ d then e
  else
    match e with
    | .bvar i .. =>
      if i < d then e
      else if _h : i - d < k then
        if h : i - d < vs.size then
          let w := vs[vs.size - 1 - (i - d)]'(by omega)
          if i - d = 0 || w.bvarB ≤ d then w
          else instRevPl vs w (i - d) d
        else e
      else Expr.mkBvar (i - k)
    | .fvar .. | .sort .. | .const .. | .lit .. => e
    | .app f a .. => Expr.mkApp (instRevPl vs f k d) (instRevPl vs a k d)
    | .lam ty body .. => Expr.mkLam (instRevPl vs ty k d) (instRevPl vs body k (d + 1))
    | .forallE ty body .. =>
      Expr.mkForallE (instRevPl vs ty k d) (instRevPl vs body k (d + 1))
    | .letE ty val body .. =>
      Expr.mkLetE (instRevPl vs ty k d) (instRevPl vs val k d) (instRevPl vs body k (d + 1))
    | .proj sn i sub .. => Expr.mkProj sn i (instRevPl vs sub k d)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

theorem instRevPl_eq (vs : Array Expr) : ∀ (k : Nat) (e : Expr) (d : Nat),
    instRevPl vs e k d = Expr.instantiateRevP vs e k d := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
    intro e
    induction e with
    | bvar i =>
      intro d; rw [instRevPl, Expr.instantiateRevP]
      by_cases hk : k = 0
      · simp [hk]
      · simp only [hk, if_false]
        split <;> try rfl
        split <;> try rfl
        split
        · rename_i hlt; split <;> try rfl
          split <;> try rfl
          exact ihk _ hlt _ _
        · rfl
    | _ => intro d; rw [instRevPl, Expr.instantiateRevP] <;> simp_all

/-! The simultaneous substitutions. Their leaf re-enters the plain walk on a
substituted value (with a smaller count); only the outer walk is memoised. -/
def instListLeaf (vs : Array Expr) (k : Nat) (e : Expr) (d : Nat) : Expr :=
  match e with
  | .bvar i .. =>
    if i < d then e
    else if i - d < k then
      if h : i - d < vs.size then
        let w := vs[i - d]
        if i - d = 0 || w.bvarB ≤ d then w
        else instListPl vs w (i - d) d
      else e
    else Expr.mkBvar (i - k)
  | _ => e
def instRevLeaf (vs : Array Expr) (k : Nat) (e : Expr) (d : Nat) : Expr :=
  match e with
  | .bvar i .. =>
    if i < d then e
    else if i - d < k then
      if h : i - d < vs.size then
        let w := vs[vs.size - 1 - (i - d)]'(by omega)
        if i - d = 0 || w.bvarB ≤ d then w
        else instRevPl vs w (i - d) d
      else e
    else Expr.mkBvar (i - k)
  | _ => e

theorem instantiateListP_rw (vs : Array Expr) (k : Nat) (e : Expr) (d : Nat) :
    Expr.instantiateListP vs e k d =
      rwP (fun e c => k == 0 || decide (e.bvarB ≤ c)) (instListLeaf vs k) (fun e _ _ _ => some e)
        Nat.succ e d := by
  induction e generalizing d <;> (rw [Expr.instantiateListP, rwP]; simp_all [instListLeaf, instListPl_eq]) <;>
    (split <;> simp_all)
theorem instantiateRevP_rw (vs : Array Expr) (k : Nat) (e : Expr) (d : Nat) :
    Expr.instantiateRevP vs e k d =
      rwP (fun e c => k == 0 || decide (e.bvarB ≤ c)) (instRevLeaf vs k) (fun e _ _ _ => some e)
        Nat.succ e d := by
  induction e generalizing d <;> (rw [Expr.instantiateRevP, rwP]; simp_all [instRevLeaf, instRevPl_eq]) <;>
    (split <;> simp_all)

def instantiateListM (vs : Array Expr) (e : Expr) (k d : Nat) : Expr :=
  (rwM (fun e c => k == 0 || decide (e.bvarB ≤ c)) (instListLeaf vs k) (fun e _ _ _ => some e)
    Nat.succ (.leaf []) e d).1
def instantiateRevM (vs : Array Expr) (e : Expr) (k d : Nat) : Expr :=
  (rwM (fun e c => k == 0 || decide (e.bvarB ≤ c)) (instRevLeaf vs k) (fun e _ _ _ => some e)
    Nat.succ (.leaf []) e d).1
theorem instantiateListP_eq_M (vs : Array Expr) (e : Expr) (k d : Nat) :
    Expr.instantiateListP vs e k d = instantiateListM vs e k d := by
  rw [instantiateListP_rw, instantiateListM, rwM_eq]
theorem instantiateRevP_eq_M (vs : Array Expr) (e : Expr) (k d : Nat) :
    Expr.instantiateRevP vs e k d = instantiateRevM vs e k d := by
  rw [instantiateRevP_rw, instantiateRevM, rwM_eq]
end ConPastel.Impl

namespace ConPastel.Leche
cake_datatype (ConPastel.Impl.ExprMemo (Nat × ConLeche.Expr))
end ConPastel.Leche

cake_replace ConLeche.Expr.liftLooseBVarsP ConPastel.Impl.liftLooseBVarsM ConPastel.Impl.liftLooseBVarsP_eq_M
cake_replace ConLeche.Expr.instantiate1P ConPastel.Impl.instantiate1M ConPastel.Impl.instantiate1P_eq_M
cake_replace ConLeche.Expr.instantiateLiftP ConPastel.Impl.instantiateLiftM ConPastel.Impl.instantiateLiftP_eq_M
cake_replace ConLeche.Expr.abstract1P ConPastel.Impl.abstract1M ConPastel.Impl.abstract1P_eq_M
cake_replace ConLeche.Expr.abstractRangeP ConPastel.Impl.abstractRangeM ConPastel.Impl.abstractRangeP_eq_M
cake_replace ConLeche.Expr.replaceFVarsP ConPastel.Impl.replaceFVarsM ConPastel.Impl.replaceFVarsP_eq_M
cake_replace ConLeche.Expr.instLevelParamsP ConPastel.Impl.instLevelParamsM ConPastel.Impl.instLevelParamsP_eq_M
cake_replace ConLeche.Expr.targetAbsP ConPastel.Impl.targetAbsM ConPastel.Impl.targetAbsP_eq_M
cake_replace ConLeche.Expr.instantiateListP ConPastel.Impl.instantiateListM ConPastel.Impl.instantiateListP_eq_M
cake_replace ConLeche.Expr.instantiateRevP ConPastel.Impl.instantiateRevM ConPastel.Impl.instantiateRevP_eq_M

/-! ## The loose-variable searches, memoised

`Expr.hasLooseBVarB` and `hasLooseBVarInP` stop at a node whose loose-variable
bound is at or below the cursor, and otherwise descend: on a shared DAG with
loose variables throughout, that is the whole tree. Both are instances of one
search, memoised on (node, cursor). -/

namespace ConPastel.Impl
open ConLeche

/-- The search: below the cut-off `cut`, a variable answers by `bv`, the
other leaves `false`; the cursor moves up by one under a binder. -/
def anyP (cut : Expr → Nat → Bool) (bv : Nat → Nat → Bool) (e : Expr) (c : Nat) : Bool :=
  if cut e c then false else
  match e with
  | .bvar j => bv j c
  | .fvar .. | .sort _ | .const .. | .lit _ => false
  | .app f a => anyP cut bv f c || anyP cut bv a c
  | .lam ty b => anyP cut bv ty c || anyP cut bv b (c + 1)
  | .forallE ty b => anyP cut bv ty c || anyP cut bv b (c + 1)
  | .letE t v b => anyP cut bv t c || anyP cut bv v c || anyP cut bv b (c + 1)
  | .proj _ _ s => anyP cut bv s c

/-- Memo entries `(node, cursor, answer)`. -/
abbrev BMemo := ExprMemo (Nat × Bool)

def findCB (e : Expr) (c : Nat) : List (Expr × Nat × Bool) → Option Bool
  | [] => none
  | (x, c', r) :: t => if c' == c && exprEqD x e then some r else findCB e c t

def BMemo.find? (e : Expr) (c : Nat) : BMemo → Nat → Option Bool
  | .leaf l, _ => findCB e c l
  | .node a b, k => if k % 2 = 0 then BMemo.find? e c a (k / 2) else BMemo.find? e c b (k / 2)

theorem findCB_sound {P : Expr → Nat × Bool → Prop} {e : Expr} {c : Nat} :
    ∀ {l : List (Expr × Nat × Bool)} {r : Bool}, (∀ p ∈ l, P p.1 p.2) → findCB e c l = some r → P e (c, r)
  | [], _, _, h => by simp [findCB] at h
  | (x, c', w) :: t, r, hl, h => by
    simp only [findCB] at h
    split at h
    · rename_i hx; cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      obtain ⟨hc, he⟩ := hx
      have := (exprEqD_iff x e).mp he; subst this; subst hc
      exact hl (x, c', _) (by simp)
    · exact findCB_sound (fun p hp => hl p (by simp [hp])) h

theorem BMemo.find?_sound {P : Expr → Nat × Bool → Prop} {e : Expr} {c : Nat} :
    ∀ {t : BMemo} {k : Nat} {r : Bool}, t.All P → BMemo.find? e c t k = some r → P e (c, r)
  | .leaf l, _, _, ht, h => findCB_sound ht h
  | .node a b, k, r, ht, h => by
    simp only [BMemo.find?] at h
    split at h
    · exact BMemo.find?_sound ht.1 h
    · exact BMemo.find?_sound ht.2 h

/-- `anyP`, memoised on (node, cursor) for the compound nodes. -/
def anyM (cut : Expr → Nat → Bool) (bv : Nat → Nat → Bool) (t : BMemo) (e : Expr) (c : Nat) :
    Bool × BMemo :=
  if cut e c then (false, t) else
  match e with
  | .bvar j => (bv j c, t)
  | .fvar .. | .sort _ | .const .. | .lit _ => (false, t)
  | .app f a =>
    match BMemo.find? e c t (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := anyM cut bv t f c
      let r2 := if r1.1 then (true, r1.2) else anyM cut bv r1.2 a c
      (r2.1, ExprMemo.insert e (c, r2.1) 16 r2.2 (ExprMemo.key e))
  | .lam ty b =>
    match BMemo.find? e c t (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := anyM cut bv t ty c
      let r2 := if r1.1 then (true, r1.2) else anyM cut bv r1.2 b (c + 1)
      (r2.1, ExprMemo.insert e (c, r2.1) 16 r2.2 (ExprMemo.key e))
  | .forallE ty b =>
    match BMemo.find? e c t (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := anyM cut bv t ty c
      let r2 := if r1.1 then (true, r1.2) else anyM cut bv r1.2 b (c + 1)
      (r2.1, ExprMemo.insert e (c, r2.1) 16 r2.2 (ExprMemo.key e))
  | .letE ty v b =>
    match BMemo.find? e c t (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := anyM cut bv t ty c
      let r2 := if r1.1 then (true, r1.2) else anyM cut bv r1.2 v c
      let r3 := if r2.1 then (true, r2.2) else anyM cut bv r2.2 b (c + 1)
      (r3.1, ExprMemo.insert e (c, r3.1) 16 r3.2 (ExprMemo.key e))
  | .proj _ _ s =>
    match BMemo.find? e c t (ExprMemo.key e) with
    | some r => (r, t)
    | none =>
      let r1 := anyM cut bv t s c
      (r1.1, ExprMemo.insert e (c, r1.1) 16 r1.2 (ExprMemo.key e))

section
variable (cut : Expr → Nat → Bool) (bv : Nat → Nat → Bool)

abbrev BGood (t : BMemo) : Prop := t.All (fun x p => p.2 = anyP cut bv x p.1)

theorem anyM_spec : ∀ (e : Expr) (c : Nat) (t : BMemo), BGood cut bv t →
    (anyM cut bv t e c).1 = anyP cut bv e c ∧ BGood cut bv (anyM cut bv t e c).2 := by
  intro e
  induction e with
  | bvar | fvar | sort | const | lit =>
    intro c t ht; rw [anyM]
    split
    · rename_i hcut; exact ⟨by rw [anyP]; simp [hcut], ht⟩
    · rename_i hcut; exact ⟨by rw [anyP]; simp [hcut], ht⟩
  | app f a ihf iha =>
    intro c t ht; rw [anyM]
    split
    · rename_i hcut; exact ⟨by rw [anyP]; simp [hcut], ht⟩
    · rename_i hcut
      split
      · rename_i r hr; exact ⟨BMemo.find?_sound (P := fun x p => p.2 = anyP cut bv x p.1) ht hr, ht⟩
      · obtain ⟨h1, h2⟩ := ihf c t ht
        by_cases hb : (anyM cut bv t f c).1 = true
        · have hp : anyP cut bv f c = true := h1 ▸ hb
          refine ⟨?_, ExprMemo.insert_all ?_ ?_⟩ <;> simp only [hb, if_true] <;>
            first | exact h2 | (rw [anyP]; simp [hcut, hp])
        · have hp : anyP cut bv f c = false := by rw [← h1]; simpa using hb
          obtain ⟨h3, h4⟩ := iha c _ h2
          refine ⟨?_, ExprMemo.insert_all ?_ ?_⟩ <;> simp only [hb, Bool.false_eq_true, if_false] <;>
            first | exact h4 | (rw [anyP]; simp [hcut, hp, h3])
  | lam ty b iht ihb =>
    intro c t ht; rw [anyM]
    split
    · rename_i hcut; exact ⟨by rw [anyP]; simp [hcut], ht⟩
    · rename_i hcut
      split
      · rename_i r hr; exact ⟨BMemo.find?_sound (P := fun x p => p.2 = anyP cut bv x p.1) ht hr, ht⟩
      · obtain ⟨h1, h2⟩ := iht c t ht
        by_cases hb : (anyM cut bv t ty c).1 = true
        · have hp : anyP cut bv ty c = true := h1 ▸ hb
          refine ⟨?_, ExprMemo.insert_all ?_ ?_⟩ <;> simp only [hb, if_true] <;>
            first | exact h2 | (rw [anyP]; simp [hcut, hp])
        · have hp : anyP cut bv ty c = false := by rw [← h1]; simpa using hb
          obtain ⟨h3, h4⟩ := ihb (c + 1) _ h2
          refine ⟨?_, ExprMemo.insert_all ?_ ?_⟩ <;> simp only [hb, Bool.false_eq_true, if_false] <;>
            first | exact h4 | (rw [anyP]; simp [hcut, hp, h3])
  | forallE ty b iht ihb =>
    intro c t ht; rw [anyM]
    split
    · rename_i hcut; exact ⟨by rw [anyP]; simp [hcut], ht⟩
    · rename_i hcut
      split
      · rename_i r hr; exact ⟨BMemo.find?_sound (P := fun x p => p.2 = anyP cut bv x p.1) ht hr, ht⟩
      · obtain ⟨h1, h2⟩ := iht c t ht
        by_cases hb : (anyM cut bv t ty c).1 = true
        · have hp : anyP cut bv ty c = true := h1 ▸ hb
          refine ⟨?_, ExprMemo.insert_all ?_ ?_⟩ <;> simp only [hb, if_true] <;>
            first | exact h2 | (rw [anyP]; simp [hcut, hp])
        · have hp : anyP cut bv ty c = false := by rw [← h1]; simpa using hb
          obtain ⟨h3, h4⟩ := ihb (c + 1) _ h2
          refine ⟨?_, ExprMemo.insert_all ?_ ?_⟩ <;> simp only [hb, Bool.false_eq_true, if_false] <;>
            first | exact h4 | (rw [anyP]; simp [hcut, hp, h3])
  | letE ty v b iht ihv ihb =>
    intro c t ht; rw [anyM]
    split
    · rename_i hcut; exact ⟨by rw [anyP]; simp [hcut], ht⟩
    · rename_i hcut
      split
      · rename_i r hr; exact ⟨BMemo.find?_sound (P := fun x p => p.2 = anyP cut bv x p.1) ht hr, ht⟩
      · obtain ⟨h1, h2⟩ := iht c t ht
        by_cases hb : (anyM cut bv t ty c).1 = true
        · have hp : anyP cut bv ty c = true := h1 ▸ hb
          refine ⟨?_, ExprMemo.insert_all ?_ ?_⟩ <;> simp only [hb, if_true] <;>
            first | exact h2 | (rw [anyP]; simp [hcut, hp])
        · have hp : anyP cut bv ty c = false := by rw [← h1]; simpa using hb
          obtain ⟨h3, h4⟩ := ihv c _ h2
          by_cases hb2 : (anyM cut bv (anyM cut bv t ty c).2 v c).1 = true
          · have hp2 : anyP cut bv v c = true := h3 ▸ hb2
            refine ⟨?_, ExprMemo.insert_all ?_ ?_⟩ <;> simp only [hb, hb2, Bool.false_eq_true, if_false, if_true] <;>
              first | exact h4 | (rw [anyP]; simp [hcut, hp, hp2])
          · have hp2 : anyP cut bv v c = false := by rw [← h3]; simpa using hb2
            obtain ⟨h5, h6⟩ := ihb (c + 1) _ h4
            refine ⟨?_, ExprMemo.insert_all ?_ ?_⟩ <;> simp only [hb, hb2, Bool.false_eq_true, if_false] <;>
              first | exact h6 | (rw [anyP]; simp [hcut, hp, hp2, h5])
  | proj sn i x ih =>
    intro c t ht; rw [anyM]
    split
    · rename_i hcut; exact ⟨by rw [anyP]; simp [hcut], ht⟩
    · rename_i hcut
      split
      · rename_i r hr; exact ⟨BMemo.find?_sound (P := fun x p => p.2 = anyP cut bv x p.1) ht hr, ht⟩
      · obtain ⟨h1, h2⟩ := ih c t ht
        refine ⟨?_, ExprMemo.insert_all ?_ h2⟩ <;> (dsimp only; rw [anyP]; simp [hcut, h1])

theorem anyM_eq (e : Expr) (c : Nat) : (anyM cut bv (.leaf []) e c).1 = anyP cut bv e c :=
  (anyM_spec cut bv e c (.leaf []) (by simp [ExprMemo.All])).1
end

def lbCut (e : Expr) (c : Nat) : Bool := decide (e.bvarB ≤ c)

theorem hasLooseBVarB_anyP : ∀ (e : Expr) (i : Nat),
    Expr.hasLooseBVarB i e = anyP lbCut (fun j c => c == j) e i := by
  intro e; induction e <;> intro i <;> rw [Expr.hasLooseBVarB, anyP] <;> simp_all [lbCut]

theorem hasLooseBVarInP_anyP (w : Nat) : ∀ (e : Expr) (d : Nat),
    Expr.hasLooseBVarInP w e d = anyP lbCut (fun j c => decide (c ≤ j) && decide (j < c + w)) e d := by
  intro e; induction e <;> intro d <;> rw [Expr.hasLooseBVarInP, anyP] <;> simp_all [lbCut]

def hasLooseBVarBM (i : Nat) (e : Expr) : Bool := (anyM lbCut (fun j c => c == j) (.leaf []) e i).1
def hasLooseBVarInM (w : Nat) (e : Expr) (d : Nat) : Bool :=
  (anyM lbCut (fun j c => decide (c ≤ j) && decide (j < c + w)) (.leaf []) e d).1

theorem hasLooseBVarB_eq_M (i : Nat) (e : Expr) : Expr.hasLooseBVarB i e = hasLooseBVarBM i e := by
  rw [hasLooseBVarB_anyP, hasLooseBVarBM, anyM_eq]
theorem hasLooseBVarInP_eq_M (w : Nat) (e : Expr) (d : Nat) :
    Expr.hasLooseBVarInP w e d = hasLooseBVarInM w e d := by
  rw [hasLooseBVarInP_anyP, hasLooseBVarInM, anyM_eq]
end ConPastel.Impl

namespace ConPastel.Leche
cake_datatype (ConPastel.Impl.ExprMemo (Nat × Bool))
end ConPastel.Leche

cake_replace ConLeche.Expr.hasLooseBVarB ConPastel.Impl.hasLooseBVarBM ConPastel.Impl.hasLooseBVarB_eq_M
cake_replace ConLeche.Expr.hasLooseBVarInP ConPastel.Impl.hasLooseBVarInM ConPastel.Impl.hasLooseBVarInP_eq_M
