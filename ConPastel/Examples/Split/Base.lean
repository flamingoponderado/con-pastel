import ConPastel.Program.Command

/-! Split translation of a mutual block (`cake_mutual_prepare` / `cake_mutual_part`
/ `cake_mutual_finish`): the block's members are solved in two modules
(`Part0`, `Part1`), which Lake builds in parallel, and `Finish` assembles the
joint theorem. -/

namespace ConPastel.Examples.Split

def sq (n : Nat) : Nat := n * n
def cube (n : Nat) : Nat := sq n * n

mutual
def a : Nat → List Nat → Nat
  | 0, l => l.length
  | n+1, l => b n (sq n :: l)
termination_by n => n
def b : Nat → List Nat → Nat
  | 0, _ => 1
  | n+1, l => c n (n :: l)
termination_by n => n
def c : Nat → List Nat → Nat
  | 0, _ => 7
  | n+1, l => a n (cube n :: l)
termination_by n => n
end

cake_mutual_prepare a

end ConPastel.Examples.Split
