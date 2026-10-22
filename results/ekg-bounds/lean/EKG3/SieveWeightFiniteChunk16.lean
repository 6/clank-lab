import EKG3.SieveWeightFiniteChunk15

/-! Kernel-checked chunk 16 of the finite range: 1280 < Q ≤ 1360.
The running total 8483305 at Q = 1280 is certified by `finiteSieveCheck_chunk15`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk16 : finiteSieveCheck 80 1280 8483305 8548349 = true := by decide +kernel

end EKG3
