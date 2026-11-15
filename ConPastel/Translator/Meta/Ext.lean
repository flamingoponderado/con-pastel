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
  ((datatypeExt.getState env).toList.find? (·.2.ty == ty)).map (·.2)

def nextStamp (env : Environment) : Nat :=
  2 + (datatypeExt.getState env).size

/-- Replacements `K ↦ (K', thm)` with `thm : ∀ xs, K xs = K' xs`: the
translator translates `K' xs` for `K xs` (for library functions whose own
definitions do not translate, e.g. recursion with proof parameters). -/
initialize replaceExt : SimplePersistentEnvExtension (Name × Name × Name) (NameMap (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (k, r, t) => m.insert k (r, t)
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m (k, r, t) => m.insert k (r, t)) m) {}
  }

/-- Rewrite rules `thm : ∀ xs, lhs = rhs` keyed by `lhs`'s head constant: a
term matching `lhs` (by unification) is translated as `rhs` (for equations
that hold only at particular arguments, e.g. `Array.foldlM`'s default bounds). -/
initialize rewriteExt : SimplePersistentEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (k, t) => m.insert k ((m.find? k).getD #[] |>.push t)
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m (k, t) =>
      m.insert k ((m.find? k).getD #[] |>.push t)) m) {}
  }

/-- Replacements under runtime assumptions `K ↦ (K', P)` with `P` a closed
proposition `∀ xs, K xs = K' xs` (a field of `RuntimeAssumptions`): every unit
takes the registered propositions as hypotheses, and `K xs` is translated as
`K' xs` (e.g. `mixHash` as its transcription `leanMixHash`). -/
initialize assumeReplaceExt : SimplePersistentEnvExtension (Name × Name × Expr) (Array (Name × Name × Expr)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun a e => a.push e
    addImportedFn := fun as => as.foldl (fun acc a => acc ++ a) #[]
  }

/-- The translation needs the datatype for `ty` first. -/
initialize needDatatypeRef : IO.Ref (Option Expr) ← IO.mkRef none

/-- Registers a datatype in place (set by the datatype module), so that a unit
needing one does not abort the whole translation. -/
initialize datatypeHookRef : IO.Ref (Expr → MetaM Unit) ←
  IO.mkRef (fun τ => throwError "cake: no datatype registration available for {τ}")

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
  lookup of the unit itself. -/
  assumes : Array Expr := #[]
  /-- The units (by name) whose certificates discharge the dependencies, in
  the order of `deps` (a key may be translated in several modules). -/
  depNames : Array Name := #[]
  /-- The other members of this unit's mutual block (their entries and
  lookups are hypotheses of the certificate, after the assumptions). -/
  peers : Array Name := #[]
  deriving Inhabited

/-- Units by key (for translation) and all units (for assembly; a key may have
been translated in several independent modules). -/
structure UnitState where
  byKey : Std.HashMap Expr UnitInfo := {}
  all : Array UnitInfo := #[]
  deriving Inhabited

initialize unitExt : SimplePersistentEnvExtension UnitInfo UnitState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun st d => { byKey := if st.byKey.contains d.key then st.byKey else st.byKey.insert d.key d,
                                all := st.all.push d }
    addImportedFn := fun as => as.foldl (fun st a => a.foldl (fun st d =>
      { byKey := if st.byKey.contains d.key then st.byKey else st.byKey.insert d.key d,
        all := st.all.push d }) st) {}
  }

def getUnit? (env : Environment) (key : Expr) : Option UnitInfo :=
  (unitExt.getState env).byKey.get? key

def allUnits (env : Environment) : Array UnitInfo :=
  (unitExt.getState env).all

/-- The current module's tag (`cake_module`): units of a tagged module get
names of their own, so independent modules can be imported together. -/
initialize cakeTagExt : EnvExtension (Option String) ← registerEnvExtension (pure none)

/-- The namespace of the current module's units. -/
def unitNamespace (env : Environment) : Name :=
  match cakeTagExt.getState env with
  | some t => Name.mkStr `ConPastel.Cake t
  | none => `ConPastel.Cake

/-- Units already registered in the current module's namespace. -/
def unitCount (env : Environment) : Nat :=
  let ns := unitNamespace env
  ((unitExt.getState env).all.filter (·.name.getPrefix == ns)).size


/-- Progress line: appended (and flushed) to the file named by `CAKE_LOG`, else stderr. -/
def cakeLog (msg : String) : IO Unit := do
  match ← IO.getEnv "CAKE_LOG" with
  | some path =>
    let h ← IO.FS.Handle.mk path .append
    h.putStrLn msg
    h.flush
  | none => IO.eprintln msg

end ConPastel.Translator.Meta
