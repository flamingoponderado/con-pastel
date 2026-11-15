import ConLeche.Kernel.NatOpPins
import ConPastel.Leche.Blob

/-!
# Pin variant 1's blobs as decoded data

Every `let`-chain blob of pin variant `_v1` (`ConLeche/Kernel/NatOpPins.lean`) is
translated through `decodeBlob` (`ConPastel.Leche.Blob`); the equations are
kernel-checked here, in parallel with the other variants and the kernel stage.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000

cake_blobs "_v1"
