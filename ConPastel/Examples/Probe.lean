import ConPastel.Translator.Prims
import ConPastel.Translator.Meta.Datatype
open Lean Elab Command

namespace ConPastel.Examples.Probe
open ConPastel.Translator.Meta

/-- Try translating each term; report success or the error. -/
elab "cake_probe " ts:(colGt term:max)+ : command => do
  for t in ts do
    let key ← liftTermElabM do
      let key ← instantiateMVars (← Term.elabTerm t none)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars key
    try
      cakeUnitCmd key
      logInfo m!"OK {key}"
    catch e =>
      logInfo m!"FAIL {key}: {e.toMessageData}"

cake_probe (@Array.size Nat) (@List.length Nat) (@Array.toList Nat) (Nat.beq) (Nat.ble) (@Array.push Nat)
  (UInt64.toNat) (UInt64.add) (UInt64.ofNat) (Nat.decEq) (instDecidableEqNat) (Nat.decLt)
  (ByteArray.size) (@Option.getD Nat) (@List.reverse Nat) (@List.append Nat)

end ConPastel.Examples.Probe

namespace ConPastel.Examples.Probe
cake_probe (@Option.getD Nat) (@Option.map Nat Nat) (@Option.bind Nat Nat)
end ConPastel.Examples.Probe
