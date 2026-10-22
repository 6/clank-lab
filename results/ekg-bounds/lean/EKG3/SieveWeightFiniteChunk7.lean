import EKG3.SieveWeightFiniteChunk6

/-! Kernel-checked chunk 7 of the finite range: 560 < Q ≤ 640.
The running total 7659199 at Q = 560 is certified by `finiteSieveCheck_chunk6`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk7 : finiteSieveCheck 80 560 7659199 7793255 = true := by decide +kernel

end EKG3
