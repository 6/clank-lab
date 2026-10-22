import EKG3.SieveWeightFiniteChunk7

/-! Kernel-checked chunk 8 of the finite range: 640 < Q ≤ 720.
The running total 7793255 at Q = 640 is certified by `finiteSieveCheck_chunk7`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk8 : finiteSieveCheck 80 640 7793255 7919079 = true := by decide +kernel

end EKG3
