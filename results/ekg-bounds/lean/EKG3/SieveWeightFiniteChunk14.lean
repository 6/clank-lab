import EKG3.SieveWeightFiniteChunk13

/-! Kernel-checked chunk 14 of the finite range: 1120 < Q ≤ 1200.
The running total 8350771 at Q = 1120 is certified by `finiteSieveCheck_chunk13`.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk14 : finiteSieveCheck 80 1120 8350771 8421274 = true := by decide +kernel

end EKG3
