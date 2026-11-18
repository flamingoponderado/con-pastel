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

-- the equality memo of `Expr.beqMemo` (`beqGoX`)
namespace ConPastel.Leche
cake_datatype (ConLeche.Expr.EqPair)
cake_datatype (Std.DHashMap.Internal.AssocList Nat fun (x : Nat) => ConLeche.Expr.EqPair)
cake_datatype (Std.DHashMap.Raw Nat fun (x : Nat) => ConLeche.Expr.EqPair)
cake_datatype (ConLeche.Expr.BeqSt)
cake_datatype (Option (Std.DHashMap.Internal.AssocList Nat fun (x : Nat) => ConLeche.Expr.EqPair))
end ConPastel.Leche
