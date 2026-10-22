import EKG3.SieveWeightFiniteChunk14

/-! Kernel-checked chunk 15 of the finite range: 1200 < Q ≤ 1280.
The running total 8421274 at Q = 1200 is certified by `finiteSieveCheck_chunk14`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk15 : finiteSieveCheck 80 1200 8421274 8483305 = true := by decide +kernel

end EKG3
