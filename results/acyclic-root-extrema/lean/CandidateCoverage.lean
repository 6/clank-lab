import TreeBridge
import ComparatorCounts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BBPSplitStar
theorem candidate_tree : CoverTree candidate (List.finRange 12) ∅ := by
  iterate 9 (all_goals constructor)
  all_goals decide +kernel

theorem candidate_coverage : FullCoverage candidate :=
  fullCoverage_of_coverTree candidate candidate_tree
end BBPSplitStar
