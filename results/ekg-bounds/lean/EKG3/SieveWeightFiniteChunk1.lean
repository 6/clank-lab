import EKG3.SieveWeightFiniteChunk0

/-! Kernel-checked chunk 1 of the finite range: 80 < Q ≤ 160.
The running total 5728076 at Q = 80 is certified by `finiteSieveCheck_chunk0`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk1 : finiteSieveCheck 80 80 5728076 6397778 = true := by decide +kernel

end EKG3
