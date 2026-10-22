import EKG3.SieveWeightFiniteChunk3

/-! Kernel-checked chunk 4 of the finite range: 320 < Q ≤ 400.
The running total 7098247 at Q = 320 is certified by `finiteSieveCheck_chunk3`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk4 : finiteSieveCheck 80 320 7098247 7316666 = true := by decide +kernel

end EKG3
