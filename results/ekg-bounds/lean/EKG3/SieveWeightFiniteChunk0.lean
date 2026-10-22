import EKG3.SieveWeightRounded

/-! Kernel-checked chunk 0 of the finite range: 0 < Q ≤ 80.
Each chunk imports the previous one so that the chunks are checked one at a
time and the peak memory stays that of a single chunk. -/
namespace EKG3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteSieveCheck_chunk0 : finiteSieveCheck 80 0 0 5728076 = true := by decide +kernel

end EKG3
