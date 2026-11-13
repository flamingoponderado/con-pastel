import Lean

/-! # Registries shared by the translator commands -/

namespace ConPastel.Translator.Meta
open Lean

structure DatatypeInfo where
  name : Name
  stamp : Nat
  ctors : Array (Name × Nat)
  deriving Inhabited

initialize datatypeExt : SimplePersistentEnvExtension DatatypeInfo (NameMap DatatypeInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m d => m.insert d.name d
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m d => m.insert d.name d) m) {}
  }

def getDatatype? (env : Environment) (n : Name) : Option DatatypeInfo :=
  (datatypeExt.getState env).find? n

def nextStamp (env : Environment) : Nat :=
  2 + (datatypeExt.getState env).size

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

/-- A translated Lean constant. -/
structure UnitInfo where
  const : Name
  /-- CakeML variable the unit is bound to. -/
  cname : String
  kind : UnitKind
  /-- The certificate theorem. Its hypotheses, in order: the closure
  environment `envC`, the group `funs`, distinctness of its names, this unit's
  entry (`findRecFun`), `HasBoolCons`, `HasListCons`, one `cakeHasCons` per
  datatype in `datatypes`, the lookup of this unit in the group, then for each
  dependency its lookup and its certificate. -/
  cert : Name
  datatypes : Array Name
  deps : Array Name
  deriving Inhabited

initialize unitExt : SimplePersistentEnvExtension UnitInfo (NameMap UnitInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m d => m.insert d.const d
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m d => m.insert d.const d) m) {}
  }

def getUnit? (env : Environment) (n : Name) : Option UnitInfo :=
  (unitExt.getState env).find? n

def unitCount (env : Environment) : Nat :=
  (unitExt.getState env).size

end ConPastel.Translator.Meta
