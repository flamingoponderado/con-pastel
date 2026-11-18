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

/-- The pointer test at `Expr`: equal hashes, then CakeML's `=` (a complete
decision, so the continuation is never needed); unequal hashes decide. -/
theorem ptrDecEq_expr (a b : Expr) (k : Unit → Decidable (a = b)) :
    ConLeche.ptrDecEq a b k =
      if hh : (a.data == b.data) = true then
        (if h : exprEqB a b = true then isTrue (exprEqB_sound h)
         else isFalse (fun e => h (by subst e; exact decide_eq_true rfl)))
      else isFalse (data_ne (by simpa using hh)) :=
  Subsingleton.elim _ _

theorem withPtrEq_expr (a b : Expr) (k : Unit → Bool) (h : a = b → k () = true) :
    withPtrEq a b k h = ((a.data == b.data && exprEqB a b) || k ()) := by
  show k () = _
  by_cases he : exprEqB a b = true
  · rw [h (exprEqB_sound he)]; simp
  · simp [he]

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
  | (x, v) :: t => if x.data == e.data && exprEqB x e then some v else findL e t

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
    · rename_i hx; cases h; have := exprEqB_sound (Bool.and_eq_true _ _ ▸ hx).2; subst this
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
