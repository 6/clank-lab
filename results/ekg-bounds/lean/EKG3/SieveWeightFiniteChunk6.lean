import EKG3.SieveWeightFiniteChunk5

/-! Kernel-checked chunk 6 of the finite range: 480 < Q ≤ 560.
The running total 7511970 at Q = 480 is certified by `finiteSieveCheck_chunk5`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk6 : finiteSieveCheck 80 480 7511970 7659199 = true := by decide +kernel

end EKG3
