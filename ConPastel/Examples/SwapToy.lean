import ConPastel.Program.Command
import ConPastel.Translator.Replace

/-! # Swapping tables of a state record around a computation -/

namespace ConPastel.Examples.SwapToy
open ConPastel.Translator

structure St where
  m₁ : Std.HashMap Nat Nat := {}
  m₂ : Std.HashMap Nat Bool := {}
  e₁ : Std.HashMap Nat Nat := {}
  e₂ : Std.HashMap Nat Bool := {}
  k : Nat := 0

cake_datatype (Std.DHashMap.Internal.AssocList Nat fun (_ : Nat) => Nat)
cake_datatype (Std.DHashMap.Internal.AssocList Nat fun (_ : Nat) => Bool)
cake_state_record St (·.m₁) (·.m₂) (·.e₁) (·.e₂) with (·.k)
cake_state_swap St [0, 1] [2, 3]

abbrev M := StateT St (Except Nat)

def enter (st : St) : St := { st with m₁ := st.e₁, m₂ := st.e₂, e₁ := {}, e₂ := {} }
def leave (st₂ st : St) : St := { st₂ with e₁ := st₂.m₁, e₂ := st₂.m₂, m₁ := st.m₁, m₂ := st.m₂ }

def put (n : Nat) : M Unit := hmInsertD (·.m₁) (fun st m => { st with m₁ := m }) n (n + 1)

/-- Insert `ns` normally, `es` in the swapped tables; count both maps after. -/
def run (ns es : List Nat) : M (Nat × Nat) := do
  ns.forM put
  swapRun enter leave (es.forM put)
  let a ← hmSize (·.m₁)
  let b ← hmSize (·.e₁)
  pure (a, b)

def check (l : List Nat) : Bool :=
  let ns := l.take 10
  let es := l.drop 10
  match runRef ({} : St) (run ns es) with
  | .ok (a, b) => a == ns.eraseDups.length && b == es.eraseDups.length
  | .error _ => false

cake_unit check
cake_program swapToy check
#print axioms swapToy.correct

end ConPastel.Examples.SwapToy
