import ConPastel.Program.Command
import ConPastel.Translator.Replace

/-! # A state record of hash tables updated in place -/

namespace ConPastel.Examples.RecToy
open ConPastel.Translator

structure St where
  sq : Std.HashMap Nat Nat := {}
  seen : Std.HashMap Nat Bool := {}
  bound : Nat := 0

cake_datatype (Std.DHashMap.Internal.AssocList Nat fun (_ : Nat) => Nat)
cake_datatype (Std.DHashMap.Internal.AssocList Nat fun (_ : Nat) => Bool)
cake_state_record St (·.sq) (·.seen) with (·.bound)

abbrev M := StateT St (Except Nat)

/-- `k * k`, memoized in `sq`. -/
def square (k : Nat) : M Nat := do
  match ← hmFind (·.sq) k with
  | some r => pure r
  | none =>
    let r := k * k
    hmInsertD (·.sq) (fun st m => { st with sq := m }) k r
    pure r

def step : List Nat → M Nat
  | [] => hmSize (·.sq)
  | k :: ks => do
    let b ← stRead (·.bound)
    if k > b then throw k else
    let _ ← square k
    hmInsertD (·.seen) (fun st m => { st with seen := m }) k true
    step ks

/-- Square everything below `100` (repeats hit the memo); count the distinct keys. -/
def countDistinct (l : List Nat) : Bool :=
  match runRef ({ bound := 100 } : St) (step (l.map (· % 100))) with
  | .ok n => n == (l.map (· % 100)).eraseDups.length
  | .error _ => false

cake_unit countDistinct
cake_program recToy countDistinct
#print axioms recToy.correct

end ConPastel.Examples.RecToy
