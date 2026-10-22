import EKG3.SieveWeightFiniteChunk11

/-! Kernel-checked chunk 12 of the finite range: 960 < Q ≤ 1040.
The running total 8198803 at Q = 960 is certified by `finiteSieveCheck_chunk11`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk12 : finiteSieveCheck 80 960 8198803 8278093 = true := by decide +kernel

end EKG3
