import EKG3.SieveWeightFiniteChunk9

/-! Kernel-checked chunk 10 of the finite range: 800 < Q ≤ 880.
The running total 8020151 at Q = 800 is certified by `finiteSieveCheck_chunk9`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk10 : finiteSieveCheck 80 800 8020151 8109615 = true := by decide +kernel

end EKG3
