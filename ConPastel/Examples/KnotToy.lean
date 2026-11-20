import ConPastel.Program.Command
import ConPastel.Translator.Replace

/-! # The kernel's shape, over a reference

A fuel-indexed mutual block over a state record with memo fields, a
higher-order memo wrapper (getter/setter closures), `match ←` and `if ←`. -/

namespace ConPastel.Examples.KnotToy
open ConPastel.Translator

inductive Err where
  | fuel
  | bad (n : Nat)

structure St where
  memoA : List (Nat × Nat) := []
  memoB : List (Nat × Nat) := []
  hits : Nat := 0

cake_state_ref St

abbrev M := StateT St (Except Err)

def look (k : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (a, b) :: r => if a == k then some b else look k r

def memo (get' : St → List (Nat × Nat)) (set' : St → List (Nat × Nat) → St)
    (f : Nat → M Nat) : Nat → M Nat :=
  fun k => do
    match look k (get' (← get)) with
    | some r =>
      modify fun st => { st with hits := st.hits + 1 }
      pure r
    | none =>
      let r ← f k
      modify fun st => set' st ((k, r) :: get' st)
      pure r

mutual
def evenI : Nat → Nat → M Bool
  | 0, _ => throw .fuel
  | lv + 1, n => do
    if n == 0 then pure true else
    let m ← stepI lv n
    match ← oddI lv m with
    | true => pure true
    | false => pure false
termination_by lv => lv

def oddI : Nat → Nat → M Bool
  | 0, _ => throw .fuel
  | lv + 1, n => do
    if n == 0 then pure false else
    if ← evenI lv (n - 1) then pure true else pure false
termination_by lv => lv

def stepI : Nat → Nat → M Nat
  | 0, _ => throw .fuel
  | _ + 1, n =>
    memo (·.memoA) (fun st mp => { st with memoA := mp })
      (fun k => if k > 1000 then throw (.bad k) else pure (k - 1)) n
termination_by lv => lv
end

def check (n : Nat) : Bool :=
  match runRef {} (evenI (2 * n + 5) n) with
  | .ok b => b == (n % 2 == 0)
  | .error _ => false

def checkAll (l : List Nat) : Bool := l.all check

cake_unit checkAll
cake_program knotToy checkAll
#print axioms knotToy.correct

end ConPastel.Examples.KnotToy
