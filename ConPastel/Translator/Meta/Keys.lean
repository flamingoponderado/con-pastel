import ConPastel.Translator.Meta.Ext

/-!
# Unit keys

An application `f a₁ … aₙ` of a constant splits into a static prefix (type,
instance and implicit arguments, closed terms) and data arguments. The unit
key is `f` applied to the static prefix.
-/

namespace ConPastel.Translator.Meta
open Lean Meta

/-- The number of leading static arguments of `f args`. -/
def numStatic (f : Expr) (args : Array Expr) : MetaM Nat := do
  let fty ← inferType f
  forallBoundedTelescope fty args.size fun xs _ => do
    let mut k := 0
    for i in [0:xs.size] do
      let ldecl ← xs[i]!.fvarId!.getDecl
      let a := args[i]!
      let isTypeLike ← isTypeFormerType ldecl.type
      let implicitish := ldecl.binderInfo.isImplicit || ldecl.binderInfo.isInstImplicit ||
        ldecl.binderInfo.isStrictImplicit
      if (implicitish || isTypeLike || (← isClass? ldecl.type).isSome) && !a.hasFVar && !a.hasMVar then
        k := k + 1
      else break
    return k

/-- Split an application into its unit key and data arguments. -/
def splitKey (t : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let f := t.getAppFn
  unless f.isConst do return none
  let args := t.getAppArgs
  let k ← numStatic f args
  return some (mkAppN f args[:k].toArray, args[k:].toArray)

/-- Registered units whose keys occur in `e` (other than `self`). -/
partial def unitDepsOf (self : Expr) (e : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  let found ← IO.mkRef (#[] : Array Expr)
  let rec visit (e : Expr) : MetaM Unit := do
    match e with
    | .app .. | .const .. =>
      if e.getAppFn.isConst then
        if let some (key, _) ← splitKey e then
          if key != self && (getUnit? env key).isSome && !(← found.get).contains key then
            found.modify (·.push key)
      for a in e.getAppArgs do visit a
      unless e.getAppFn.isConst do visit e.getAppFn
    | .lam _ ty b _ | .forallE _ ty b _ =>
      visit ty
      withLocalDeclD `x ty fun x => visit (b.instantiate1 x)
    | .letE _ ty v b _ =>
      visit ty; visit v
      withLocalDeclD `x ty fun x => visit (b.instantiate1 x)
    | .mdata _ e' => visit e'
    | .proj _ _ e' => visit e'
    | _ => pure ()
  visit e
  found.get

end ConPastel.Translator.Meta
