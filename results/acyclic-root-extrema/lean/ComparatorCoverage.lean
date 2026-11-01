import CandidateCoverage

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BBPSplitStar
theorem comparator_tree : CoverTree (J 12) (List.finRange 12) ∅ := by
  iterate 9 (all_goals constructor)
  all_goals decide +kernel

theorem comparator_coverage : FullCoverage (J 12) :=
  fullCoverage_of_coverTree (J 12) comparator_tree
end BBPSplitStar
