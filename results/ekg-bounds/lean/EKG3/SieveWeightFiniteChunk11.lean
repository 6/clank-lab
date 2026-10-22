import EKG3.SieveWeightFiniteChunk10

/-! Kernel-checked chunk 11 of the finite range: 880 < Q ≤ 960.
The running total 8109615 at Q = 880 is certified by `finiteSieveCheck_chunk10`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk11 : finiteSieveCheck 80 880 8109615 8198803 = true := by decide +kernel

end EKG3
