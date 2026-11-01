import CandidateCounts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BBPSplitStar
theorem comparator_counts : ∀ k : Fin 13,
    countCoefficient (J 12) k =
      (![1, 12, 66, 85, 1, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 13 → ℤ) k := by
  intro k
  fin_cases k <;> decide +kernel
end BBPSplitStar
