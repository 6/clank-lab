import EKG3.SieveWeightFiniteChunk16

/-! Kernel-checked chunk 17 of the finite range: 1360 < Q ≤ 1439.
The running total 8548349 at Q = 1360 is certified by `finiteSieveCheck_chunk16`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk17 : finiteSieveCheck 79 1360 8548349 8608734 = true := by decide +kernel

end EKG3
