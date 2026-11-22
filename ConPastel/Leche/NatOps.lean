import ConPastel.Translator.Replace
import ConLeche.Cached.StateC

/-!
# Recognising a `Nat` operation's name without building the names

`NatBinOp.ofName? c` compares `c` with the fourteen operation names
(`natAddName` … `natShiftRightName`). In the translation those constants are
rebuilt, and hashed, at every use, and the test runs on every reduction step of
an application of a constant: usually none of them matches, and all fourteen
were built. `ofNameF` reads the name's shape, `Nat.<s>`, and compares strings.
-/

namespace ConPastel.Impl
open ConLeche ConLeche.Cached

theorem nameIsC_eq (c n : Name) : nameIsC c n = decide (c = n) := by
  by_cases h : c = n
  · subst h; simp [nameIsC]
  · simp [nameIsC, h]

/-- `NatBinOp.ofName?` by the name's shape: `Nat.<op>` is recognised without
building (and hashing) the fourteen operation names. -/
def natOpOfStr (s : String) : Option NatBinOp :=
  if s = "add" then some .add else if s = "sub" then some .sub
  else if s = "mul" then some .mul else if s = "pow" then some .pow
  else if s = "beq" then some .beq else if s = "ble" then some .ble
  else if s = "div" then some .div else if s = "mod" then some .mod
  else if s = "gcd" then some .gcd else if s = "land" then some .land
  else if s = "lor" then some .lor else if s = "xor" then some .xor
  else if s = "shiftLeft" then some .shiftLeft else if s = "shiftRight" then some .shiftRight
  else none

def ofNameF : Name → Option NatBinOp
  | .str (.str .anonymous t) s => if t = "Nat" then natOpOfStr s else none
  | _ => none

theorem ofName_eq_F (c : Name) : NatBinOp.ofName? c = ofNameF c := by
  simp only [NatBinOp.ofName?, nameIsC_eq]
  rcases c with _ | ⟨p, s⟩ | ⟨p, k⟩
  · simp [ofNameF, natAddName, natSubName, natMulName, natPowName, natBeqName, natBleName, natDivName,
      natModName, natGcdName, natLandName, natLorName, natXorName, natShiftLeftName, natShiftRightName]
  · by_cases hp : p = natName
    · subst hp
      simp [ofNameF, natOpOfStr, natName, natAddName, natSubName, natMulName, natPowName, natBeqName,
        natBleName, natDivName, natModName, natGcdName, natLandName, natLorName, natXorName,
        natShiftLeftName, natShiftRightName]
    · have hn : ofNameF (.str p s) = none := by
        rcases p with _ | ⟨q, t⟩ | ⟨q, k⟩
        · rfl
        · rcases q with _ | ⟨q', t'⟩ | ⟨q', k'⟩
          · have : t ≠ "Nat" := fun e => hp (by subst e; rfl)
            simp [ofNameF, this]
          · rfl
          · rfl
        · rfl
      rw [hn]
      simp [natAddName, natSubName, natMulName, natPowName, natBeqName, natBleName, natDivName,
        natModName, natGcdName, natLandName, natLorName, natXorName, natShiftLeftName, natShiftRightName,
        Name.str.injEq, hp]
  · simp [ofNameF, natAddName, natSubName, natMulName, natPowName, natBeqName, natBleName, natDivName,
      natModName, natGcdName, natLandName, natLorName, natXorName, natShiftLeftName, natShiftRightName]
end ConPastel.Impl

cake_replace ConLeche.Cached.NatBinOp.ofName? ConPastel.Impl.ofNameF ConPastel.Impl.ofName_eq_F
