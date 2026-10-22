import EKG3.SieveWeightFiniteChunk4

/-! Kernel-checked chunk 5 of the finite range: 400 < Q ≤ 480.
The running total 7316666 at Q = 400 is certified by `finiteSieveCheck_chunk4`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk5 : finiteSieveCheck 80 400 7316666 7511970 = true := by decide +kernel

end EKG3
