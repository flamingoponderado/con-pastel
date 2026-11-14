import Lean

/-! # Registries shared by the translator commands -/

namespace ConPastel.Translator.Meta
open Lean

/-- A CakeML datatype for a closed Lean inductive type `ty` (an instance, for
parameterized types). -/
structure DatatypeInfo where
  /-- The Lean type, e.g. `Option Nat`. -/
  ty : Expr
  /-- Namespace of the generated declarations (`ty`, `cakeInv`, `cakeHasCons`, …). -/
  name : Name
  stamp : Nat
  /-- Per constructor: its Lean name, its CakeML name, and which fields are data. -/
  ctors : Array (Name × String × Array Bool)
  deriving Inhabited

initialize datatypeExt : SimplePersistentEnvExtension DatatypeInfo (NameMap DatatypeInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m d => m.insert d.name d
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m d => m.insert d.name d) m) {}
  }

def allDatatypes (env : Environment) : Array DatatypeInfo :=
  ((datatypeExt.getState env).toList.map (·.2)).toArray.qsort (fun a b => a.stamp < b.stamp)

def getDatatypeByType? (env : Environment) (ty : Expr) : Option DatatypeInfo :=
  (allDatatypes env).find? (·.ty == ty)

def nextStamp (env : Environment) : Nat :=
  2 + (datatypeExt.getState env).size

/-- The translation needs the datatype for `ty` first. -/
initialize needDatatypeRef : IO.Ref (Option Expr) ← IO.mkRef none

end ConPastel.Translator.Meta

namespace ConPastel.Translator.Meta
open Lean

/-- How a unit is represented: every unit is one entry `(name, param, body)`
of the program's single recursive function group. -/
inductive UnitKind where
  /-- A function; `tupled` units take their arguments as a nested tuple. -/
  | function (param : String) (body : Name) (tupled : Bool)
  /-- A constant, as a function of `()`. -/
  | thunk (param : String) (body : Name)
  deriving Inhabited

/-- A translated unit: a Lean constant applied to its static (type, instance
and implicit) arguments. -/
structure UnitInfo where
  /-- The unit's Lean term, e.g. `@List.length Nat`. -/
  key : Expr
  /-- Namespace of the unit's generated declarations (`body`, `cert`, `tupled`). -/
  name : Name
  /-- CakeML variable the unit is bound to (`%k`). -/
  cname : String
  kind : UnitKind
  /-- The certificate theorem. Its hypotheses, in order: the closure
  environment `envC`, the group `funs`, distinctness of its names, this unit's
  entry (`findRecFun`), `HasBoolCons`, `HasListCons`, one `cakeHasCons` per
  datatype in `datatypes`, the lookup of this unit in the group, then for each
  dependency its lookup and its certificate. -/
  cert : Name
  datatypes : Array Name
  deps : Array Expr
  /-- Runtime assumptions (propositions) the certificate takes after the
  lookup of the unit itself (primitives only). -/
  assumes : Array Expr := #[]
  deriving Inhabited

initialize unitExt : SimplePersistentEnvExtension UnitInfo (Std.HashMap Expr UnitInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m d => m.insert d.key d
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m d => m.insert d.key d) m) {}
  }

def getUnit? (env : Environment) (key : Expr) : Option UnitInfo :=
  (unitExt.getState env).get? key

def unitCount (env : Environment) : Nat :=
  (unitExt.getState env).size

def allUnits (env : Environment) : Array UnitInfo :=
  (unitExt.getState env).toArray.map (·.2)


/-- Progress line: appended (and flushed) to the file named by `CAKE_LOG`, else stderr. -/
def cakeLog (msg : String) : IO Unit := do
  match ← IO.getEnv "CAKE_LOG" with
  | some path =>
    let h ← IO.FS.Handle.mk path .append
    h.putStrLn msg
    h.flush
  | none => IO.eprintln msg

end ConPastel.Translator.Meta
