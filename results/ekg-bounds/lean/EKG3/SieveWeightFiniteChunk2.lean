import EKG3.SieveWeightFiniteChunk1

/-! Kernel-checked chunk 2 of the finite range: 160 < Q ≤ 240.
The running total 6397778 at Q = 160 is certified by `finiteSieveCheck_chunk1`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk2 : finiteSieveCheck 80 160 6397778 6826936 = true := by decide +kernel

end EKG3
