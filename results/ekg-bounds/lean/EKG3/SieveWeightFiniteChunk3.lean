import EKG3.SieveWeightFiniteChunk2

/-! Kernel-checked chunk 3 of the finite range: 240 < Q ≤ 320.
The running total 6826936 at Q = 240 is certified by `finiteSieveCheck_chunk2`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk3 : finiteSieveCheck 80 240 6826936 7098247 = true := by decide +kernel

end EKG3
