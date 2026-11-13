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

/-- How a unit's value is bound in the program. -/
inductive UnitKind where
  /-- `Dlet (pvar name) exp`: the certificate is an `Eval` of `exp`. -/
  | plain (exp : Name)
  /-- `Dletrec [(name, param, body)]`: the certificate is an `Arrow` for the
  recursive closure; `tupled` units take their arguments as a nested tuple. -/
  | recursive (param : String) (body : Name) (tupled : Bool)
  deriving Inhabited

/-- A translated Lean constant. -/
structure UnitInfo where
  const : Name
  /-- CakeML variable the unit is bound to. -/
  cname : String
  kind : UnitKind
  /-- The certificate theorem. Its hypotheses, in order: the environment,
  `HasBoolCons`, one `cakeHasCons` per datatype in `datatypes`, then for
  each dependency a value, its invariant and its lookup. -/
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

end ConPastel.Translator.Meta
