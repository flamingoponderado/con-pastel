import Flapjack.PrimTypesHOL

/-!
# The initial state and environment

`primSemEnv` evaluates CakeML's primitive-types program: four exceptions
(`Bind`, `Chr`, `Div`, `Subscript`, stamps 0–3) and the datatypes `bool`
(type stamp 0) and `list` (type stamp 1). This file gives the result in
closed form.
-/

namespace ConPastel
open Flapjack Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.EvaluateHOL Flapjack.PrimTypesHOL
open Flapjack.Basis.Pure.MlString

/-- The state after the primitive-types program. -/
def initState {σ : Type} (ffi : HolFfiState σ) : State σ :=
  { clock := 0, refs := [], ffi := ffi, nextTypeStamp := 2, nextExnStamp := 4, evalState := none }

/-- The constructor environment after the primitive-types program. -/
def initCons : List (ConN × Nat × Stamp) :=
  [(ofString "::", 2, .typeStamp (ofString "::") 1),
   (ofString "[]", 0, .typeStamp (ofString "[]") 1),
   (ofString "True", 0, .typeStamp (ofString "True") 0),
   (ofString "False", 0, .typeStamp (ofString "False") 0),
   (ofString "Subscript", 0, .exnStamp 3),
   (ofString "Div", 0, .exnStamp 2),
   (ofString "Chr", 0, .exnStamp 1),
   (ofString "Bind", 0, .exnStamp 0)]

/-- The environment after the primitive-types program: no values, and the
constructors in `initCons`. -/
def initEnv : SemEnv Value := { v := .bind [] [], c := .bind initCons [] }

theorem primSemEnv_eq {σ : Type} (ffi : HolFfiState σ) :
    primSemEnv ffi = some (initState ffi, initEnv) := by
  simp +decide [primSemEnv, addToSemEnv, primTypesProgram, evaluateDecs, fixClock,
    combineDecResult, extendDecEnv, buildTdefs, buildConstrs, nsAppend, nsSing, nsEmpty,
    alistToNs, initState, initEnv, initCons]

end ConPastel
