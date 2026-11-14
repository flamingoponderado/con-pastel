import ConPastel.Examples.Probe
import ConPastel.Spec

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace ConPastel.Examples.ProbeLeche
cake_probe ConPastel.conLecheResult
end ConPastel.Examples.ProbeLeche
