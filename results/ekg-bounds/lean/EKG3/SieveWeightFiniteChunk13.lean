import EKG3.SieveWeightFiniteChunk12

/-! Kernel-checked chunk 13 of the finite range: 1040 < Q ≤ 1120.
The running total 8278093 at Q = 1040 is certified by `finiteSieveCheck_chunk12`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk13 : finiteSieveCheck 80 1040 8278093 8350771 = true := by decide +kernel

end EKG3
