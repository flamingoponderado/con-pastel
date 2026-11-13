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
