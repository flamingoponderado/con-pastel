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
  /-- Cached computed fields (`cake_cached`): stored first in every constructor. -/
  cached : Array Name := #[]
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

/-- Cached computed fields per inductive type (`cake_cached T f₁ …`): each
`fᵢ : T → _` is stored in every CakeML constructor of `T`, so reading it is a
projection (as Lean's `@[computed_field]`s are) instead of a recomputation. -/
initialize cachedExt : SimplePersistentEnvExtension (Name × Array Name) (NameMap (Array Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (k, fs) => m.insert k fs
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m (k, fs) => m.insert k fs) m) {}
  }

def getCached (env : Environment) (I : Name) : Array Name :=
  ((cachedExt.getState env).find? I).getD #[]

/-- The datatype and index of a cached field `f`, if it is one. -/
def cachedFieldOf? (env : Environment) (f : Name) : Option (DatatypeInfo × Nat) :=
  ((datatypeExt.getState env).toList.findSome? fun (_, d) =>
    (d.cached.findIdx? (· == f)).map (d, ·))

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

/-- Ghost types (`cake_ghost T`): refined by `GHOST T`, every value
translated as `()`. -/
initialize ghostExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun as => as.foldl (fun acc a => a.foldl (·.insert ·) acc) {}
  }

/-- State types held in a reference (`cake_state_ref T`): `StateT T (Except ε) α`
is refined by `MRET (refRel (invOf T)) …`, a function of the state's handle. -/
initialize stateRefExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun as => as.foldl (fun acc a => a.foldl (·.insert ·) acc) {}
  }

/-- Element types of array states (`cake_state_array T`): `StateT (Array T) (Except ε) α`
is refined by `MRET (arrRel (invOf T)) …`, the state a CakeML `Array.array`. -/
initialize stateArrExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun as => as.foldl (fun acc a => a.foldl (·.insert ·) acc) {}
  }

/-- A state record of hash tables (`cake_state_record`): `recRel tabs plain`,
the accessors of its hash-map fields (in `tabs` order) and of its plain part. -/
structure StateRecInfo where
  tabs : Name
  plain : Name
  accs : Array Name
  plainAcc : Name
  deriving Inhabited

initialize stateRecExt : SimplePersistentEnvExtension (Name × StateRecInfo) (NameMap StateRecInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (k, v) => m.insert k v
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m (k, v) => m.insert k v) m) {}
  }

/-- The translation needs the datatype for `ty` first. -/
initialize needDatatypeRef : IO.Ref (Option Expr) ← IO.mkRef none

/-- Every unit key / datatype requested since the last reset, from any thread
(appended atomically): a parallel round of member solves collects all its
requests, so they are translated together before one retry. -/
initialize needUnitsAllRef : IO.Ref (Array Expr) ← IO.mkRef #[]
initialize needDatatypesAllRef : IO.Ref (Array Expr) ← IO.mkRef #[]

/-- Further units the failed parallel round needed (besides `needUnitRef`'s). -/
initialize pendingUnitsRef : IO.Ref (Array Expr) ← IO.mkRef #[]

/-- The current unit attempt collects missing units instead of aborting at the
first (`translateUnit`; the attempt is then discarded and retried once). -/
initialize collectAllRef : IO.Ref Bool ← IO.mkRef false

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

/-- How a mutual block is translated when it is split over several modules
(`cake_mutual_prepare` / `cake_mutual_part` / `cake_mutual_finish`), so that
Lake solves its members in separate processes:
* `prepare`: the shared declarations (tupled forms), no solving;
* `part j n`: solve the members `i` with `i % n = j`, each as a closed theorem
  `u.step` over the block's hypotheses, with its body `u.mbody`;
* `finish`: assemble the joint theorem from every part's `u.step`. -/
inductive SplitMode where
  | prepare
  | part (j n : Nat)
  | finish
  deriving Inhabited, Repr

/-- The block being split (named by one of its members) and the mode. -/
initialize mutualSplitRef : IO.Ref (Option (Name × SplitMode)) ← IO.mkRef none

/-- Extra dependencies of a split block (by the member named in
`cake_mutual_prepare`): units its members need that the dependency pre-pass
does not find. Every module of the block uses the same list, so the block's
hypotheses are the same in all of them. -/
initialize splitExtraExt : SimplePersistentEnvExtension (Name × Array Expr) (NameMap (Array Expr)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (k, v) => m.insert k v
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m (k, v) => m.insert k v) m) {}
  }

end ConPastel.Translator.Meta
