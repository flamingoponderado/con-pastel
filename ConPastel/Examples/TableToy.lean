import ConPastel.Program.Command
import ConPastel.Translator.Replace

/-! # Std's hash map operations, translated as in-place table code -/

namespace ConPastel.Examples.TableToy
open ConPastel.Translator

cake_unit (@insertM Nat Nat Nat _ _)
cake_unit (@getM Nat Nat Nat _ _)
cake_unit (@emptyM Nat Nat Nat)

end ConPastel.Examples.TableToy
