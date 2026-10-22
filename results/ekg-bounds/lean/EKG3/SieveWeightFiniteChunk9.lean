import EKG3.SieveWeightFiniteChunk8

/-! Kernel-checked chunk 9 of the finite range: 720 < Q ≤ 800.
The running total 7919079 at Q = 720 is certified by `finiteSieveCheck_chunk8`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk9 : finiteSieveCheck 80 720 7919079 8020151 = true := by decide +kernel

end EKG3
