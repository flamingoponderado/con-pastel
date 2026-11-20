import ConPastel.Main.Code
import ConPastel.Spec

/-!
# Translation stage: the datatypes of the kernel's dependencies

The dependencies of the kernel's mutual block are translated by independent
modules (`cake_module`, `ConPastel.Leche.KernelDeps.*`) over this one, so that
Lake builds them in parallel. Datatypes must be shared by every module that
passes their values to each other, so they are registered here, in the base
chain, in the order the translator would register them.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option linter.all false

namespace ConPastel.Leche
-- con-leche's `@[computed_field]`s are stored in the CakeML constructors (as in
-- Lean's runtime): reading one is a projection, not a walk over the term. So is
-- `depthP` (con-leche runs it as a memoized walk, which the translation replaces
-- by the plain descent: exponential on a shared DAG)
cake_cached ConLeche.Name ConLeche.Name.hashData
cake_cached ConLeche.Level ConLeche.Level.hashData
cake_cached ConLeche.Expr ConLeche.Expr.data ConLeche.Expr.depthP

cake_datatype (ConLeche.Name)
cake_datatype (ConLeche.Level)
cake_datatype (ConLeche.Literal)
cake_datatype (ConLeche.Expr)
cake_datatype (Option ConLeche.Expr)
cake_datatype (Std.DHashMap.Internal.AssocList (ConLeche.Name × List ConLeche.Level) fun (x : ConLeche.Name × List ConLeche.Level) => ConLeche.Expr)
cake_datatype (Std.DHashMap.Raw (ConLeche.Name × List ConLeche.Level) fun (x : ConLeche.Name × List ConLeche.Level) => ConLeche.Expr)
cake_datatype (Std.DHashMap.Internal.AssocList (ConLeche.Name × ConLeche.Name × List ConLeche.Level) fun (x : ConLeche.Name × ConLeche.Name × List ConLeche.Level) => ConLeche.Expr)
cake_datatype (Std.DHashMap.Raw (ConLeche.Name × ConLeche.Name × List ConLeche.Level) fun (x : ConLeche.Name × ConLeche.Name × List ConLeche.Level) => ConLeche.Expr)
cake_datatype (Std.DHashMap.Internal.AssocList ConLeche.Expr fun (x : ConLeche.Expr) => ConLeche.Expr)
cake_datatype (Std.DHashMap.Raw ConLeche.Expr fun (x : ConLeche.Expr) => ConLeche.Expr)
cake_datatype (Std.DHashMap.Internal.AssocList (ConLeche.Expr × ConLeche.Expr) fun (x : ConLeche.Expr × ConLeche.Expr) => Bool)
cake_datatype (Std.DHashMap.Raw (ConLeche.Expr × ConLeche.Expr) fun (x : ConLeche.Expr × ConLeche.Expr) => Bool)
cake_datatype (Std.DHashMap.Internal.AssocList ConLeche.Level fun (x : ConLeche.Level) => ConLeche.Level)
cake_datatype (Std.DHashMap.Raw ConLeche.Level fun (x : ConLeche.Level) => ConLeche.Level)
cake_datatype (Std.DHashMap.Internal.AssocList ConLeche.Level fun (x : ConLeche.Level) => Bool)
cake_datatype (Std.DHashMap.Raw ConLeche.Level fun (x : ConLeche.Level) => Bool)
cake_datatype (Std.DHashMap.Internal.AssocList (ConLeche.Level × ConLeche.Level) fun (x : ConLeche.Level × ConLeche.Level) => Bool)
cake_datatype (Std.DHashMap.Raw (ConLeche.Level × ConLeche.Level) fun (x : ConLeche.Level × ConLeche.Level) => Bool)
cake_datatype (Std.DHashMap.Internal.AssocList (ConLeche.Expr × List ConLeche.Expr × Nat) fun (x : ConLeche.Expr × List ConLeche.Expr × Nat) => ConLeche.Expr)
cake_datatype (Std.DHashMap.Raw (ConLeche.Expr × List ConLeche.Expr × Nat) fun (x : ConLeche.Expr × List ConLeche.Expr × Nat) => ConLeche.Expr)
cake_datatype (ConLeche.Cached.ModeMemos)
cake_datatype (ConLeche.Cached.CState)
-- the kernel's state is held in a CakeML reference: `CheckCM` computations are
-- translated as code updating it (`EvalM`), run by `declStep` on a fresh one
cake_state_ref ConLeche.Cached.CState
cake_datatype (Except ConLeche.CheckError (Option ConLeche.Expr × ConLeche.Cached.CState))
cake_datatype (Except ConLeche.CheckError (ConLeche.Name × ConLeche.Cached.CState))
cake_datatype (Option UInt8)
cake_datatype (ConLeche.ConstantVal)
cake_datatype (ConLeche.ReducibilityHint)
cake_datatype (ConLeche.IndCaps)
cake_datatype (ConLeche.RecRuleFire)
cake_datatype (ConLeche.RecRule)
cake_datatype (ConLeche.ConstantInfo)
cake_datatype (ConLeche.ProjTable)
cake_datatype (ConLeche.Env)
cake_datatype (Std.DHashMap.Internal.AssocList ConLeche.Name fun (x : ConLeche.Name) => ConLeche.ConstantInfo)
cake_datatype (Std.DHashMap.Raw ConLeche.Name fun (x : ConLeche.Name) => ConLeche.ConstantInfo)
cake_datatype (Std.DHashMap.Internal.AssocList ConLeche.Name fun (x : ConLeche.Name) => Nat × ConLeche.ConstantInfo)
cake_datatype (Std.DHashMap.Raw ConLeche.Name fun (x : ConLeche.Name) => Nat × ConLeche.ConstantInfo)
cake_datatype (Std.DHashMap.Internal.AssocList ConLeche.Name fun (x : ConLeche.Name) => Nat × ConLeche.ProjTable)
cake_datatype (Std.DHashMap.Raw ConLeche.Name fun (x : ConLeche.Name) => Nat × ConLeche.ProjTable)
cake_datatype (ConLeche.FBase)
cake_datatype (Std.DHashMap.Internal.AssocList ConLeche.Name fun (x : ConLeche.Name) => ConLeche.ProjTable)
cake_datatype (Std.DHashMap.Raw ConLeche.Name fun (x : ConLeche.Name) => ConLeche.ProjTable)
cake_datatype (ConLeche.FEnv)
cake_datatype (Option ConLeche.ConstantInfo)
cake_datatype (Option (Nat × ConLeche.ConstantInfo))
cake_datatype (Option (Std.DHashMap.Internal.AssocList ConLeche.Name fun (x : ConLeche.Name) => Nat × ConLeche.ConstantInfo))
cake_datatype (Option (Std.DHashMap.Internal.AssocList ConLeche.Name fun (x : ConLeche.Name) => ConLeche.ConstantInfo))
cake_datatype (Except ConLeche.CheckError (ConLeche.Expr × ConLeche.Cached.CState))
cake_datatype (Option Nat)
cake_datatype (Except ConLeche.CheckError (Option Nat × ConLeche.Cached.CState))
cake_datatype (Except ConLeche.CheckError (Nat × ConLeche.Cached.CState))
cake_datatype (Except ConLeche.CheckError (ConLeche.Cached.CState × ConLeche.Cached.CState))
cake_datatype (Except ConLeche.CheckError (Prod PUnit.{1} ConLeche.Cached.CState))
cake_datatype (Except ConLeche.CheckError PUnit.{1})
cake_datatype (ConLeche.Cached.NatBinOp)
cake_datatype (Option ConLeche.Cached.NatBinOp)
cake_datatype (Option ConLeche.CheckError)
cake_datatype (Except ConLeche.CheckError (Option ConLeche.Expr))
cake_datatype (Except ConLeche.CheckError ConLeche.Expr)
cake_datatype (Option (Std.DHashMap.Internal.AssocList ConLeche.Expr fun (x : ConLeche.Expr) => ConLeche.Expr))
cake_datatype (Except ConLeche.CheckError (List ConLeche.Expr × ConLeche.Cached.CState))
cake_datatype (Option (Std.DHashMap.Internal.AssocList (ConLeche.Name × List ConLeche.Level) fun (x : ConLeche.Name × List ConLeche.Level) => ConLeche.Expr))
cake_datatype (ConLeche.WhnfStep)
cake_datatype (Except ConLeche.CheckError (ConLeche.WhnfStep × ConLeche.Cached.CState))
cake_datatype (Except ConLeche.CheckError (Array ConLeche.Expr × ConLeche.Cached.CState))
cake_datatype (Std.DHashMap.Internal.AssocList ConLeche.Expr fun (x : ConLeche.Expr) => Nat)
cake_datatype (Std.DHashMap.Raw ConLeche.Expr fun (x : ConLeche.Expr) => Nat)
cake_datatype (Option (Std.DHashMap.Internal.AssocList ConLeche.Expr fun (x : ConLeche.Expr) => Nat))
cake_datatype (Except ConLeche.CheckError ConLeche.WhnfStep)
cake_datatype (ConLeche.ProjEntry)
cake_datatype (Option ConLeche.ProjEntry)
cake_datatype (Option ConLeche.ProjTable)
cake_datatype (Option (Std.DHashMap.Internal.AssocList ConLeche.Name fun (x : ConLeche.Name) => ConLeche.ProjTable))
cake_datatype (Option (Nat × ConLeche.ProjTable))
cake_datatype (Option (Std.DHashMap.Internal.AssocList ConLeche.Name fun (x : ConLeche.Name) => Nat × ConLeche.ProjTable))
cake_datatype (Except ConLeche.CheckError (Bool × ConLeche.Cached.CState))
cake_datatype (ConLeche.CheckMode)
cake_datatype (Option (Array Char))
cake_datatype (Option Char)
cake_datatype (ByteArray.utf8DecodeChar?.FirstByte)
cake_datatype (Option ConLeche.RecRule)
cake_datatype (Option (ConLeche.ConstantVal × ConLeche.IndCaps))
cake_datatype (Option Bool)
cake_datatype (Except ConLeche.CheckError (Option Bool × ConLeche.Cached.CState))
cake_datatype (Option ConLeche.Level)
cake_datatype (Option (Std.DHashMap.Internal.AssocList (ConLeche.Level × ConLeche.Level) fun (x : ConLeche.Level × ConLeche.Level) => Bool))
cake_datatype (Option (Std.DHashMap.Internal.AssocList ConLeche.Level fun (x : ConLeche.Level) => ConLeche.Level))
cake_datatype (Except ConLeche.CheckError Bool)
cake_datatype (Except ConLeche.CheckError (List ConLeche.Level × ConLeche.Cached.CState))
cake_datatype (Option (Std.DHashMap.Internal.AssocList (ConLeche.Name × ConLeche.Name × List ConLeche.Level) fun (x : ConLeche.Name × ConLeche.Name × List ConLeche.Level) => ConLeche.Expr))
cake_datatype (Option (Std.DHashMap.Internal.AssocList (ConLeche.Expr × ConLeche.Expr) fun (x : ConLeche.Expr × ConLeche.Expr) => Bool))
cake_datatype (ConLeche.LazyRes)
cake_datatype (Except ConLeche.CheckError (ConLeche.LazyRes × ConLeche.Cached.CState))
cake_datatype (Except ConLeche.CheckError (ConLeche.Level × ConLeche.Cached.CState))
cake_datatype (ConLeche.Display.Acc)
cake_datatype (String ⊕ Nat)
cake_datatype (Except ConLeche.CheckError ConLeche.Level)
cake_datatype (Except ConLeche.CheckError (Option ConLeche.Level × ConLeche.Cached.CState))
cake_datatype (Option (List (Nat × ConLeche.Expr)))
cake_datatype (Option (List ConLeche.Expr × List ConLeche.Expr × ConLeche.Expr))
cake_datatype (ConLeche.PropWhen)
cake_datatype (Except ConLeche.CheckError (Option ConLeche.Level))
cake_datatype (Option ConLeche.Cached.ModeMemos)
cake_datatype (Except ConLeche.CheckError (Option ConLeche.Cached.ModeMemos × ConLeche.Cached.CState))
cake_datatype (Option (ConLeche.Expr × Nat))
cake_datatype (ConLeche.DeltaStep)
cake_datatype (Except ConLeche.CheckError (ConLeche.DeltaStep × ConLeche.Cached.CState))
cake_datatype (Except ConLeche.CheckError (ConLeche.ReducibilityHint × ConLeche.Cached.CState))
cake_datatype (Option (ConLeche.Expr × ConLeche.Expr × ConLeche.Expr × ConLeche.Expr))
cake_datatype (Except ConLeche.CheckError ConLeche.LazyRes)
cake_datatype (Option ConLeche.PropWhen)
cake_datatype (Option (Nat × Nat))
cake_datatype (Option (Std.DHashMap.Internal.AssocList (ConLeche.Expr × List ConLeche.Expr × Nat) fun (x : ConLeche.Expr × List ConLeche.Expr × Nat) => ConLeche.Expr))
cake_datatype (Std.DHashMap.Internal.AssocList ConLeche.Expr fun (x : ConLeche.Expr) => PUnit.{1})
cake_datatype (Std.DHashMap.Raw ConLeche.Expr fun (x : ConLeche.Expr) => PUnit.{1})
cake_datatype (Option PUnit.{1})
cake_datatype (Option (Std.DHashMap.Internal.AssocList ConLeche.Expr fun (x : ConLeche.Expr) => PUnit.{1}))


open ConLeche ConLeche.Cached in
/-- `declStep`, the record's check run on a fresh reference (`runRef`). -/
def declStepR (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat) (p : Nat × FEnv)
    (pd : Declaration) : Except (CheckError × Nat) (Nat × FEnv) :=
  if andPinOk pd then
    match ConPastel.Translator.runRef ({ maxNatSize := maxNatSize } : CState)
        (checkDeclStepC mode pins p.2 pd) with
    | .ok fe' => .ok (p.1 + 1, fe')
    | .error e => .error (e, p.1)
  else .error (.invalid "`And` must be the standard `And`", p.1)

open ConLeche ConLeche.Cached in
theorem declStep_eq (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat) :
    declStep mode pins maxNatSize = declStepR mode pins maxNatSize := by
  funext p pd
  unfold declStep declStepR ConPastel.Translator.runRef
  split
  · cases checkDeclStepC mode pins p.2 pd { maxNatSize := maxNatSize } <;> rfl
  · rfl

end ConPastel.Leche

cake_replace ConLeche.Cached.declStep ConPastel.Leche.declStepR ConPastel.Leche.declStep_eq
