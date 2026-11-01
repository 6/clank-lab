import CandidateCoverage
import ComparatorCoverage
import CandidateCounts
import ComparatorCounts

namespace BBPSplitStar
theorem candidate_finite_polynomial : finitePolynomial candidate = expectedCandidate := by
  ext k
  rw [finitePolynomial_coeff]
  by_cases hk : k < 13
  · have hc := candidate_counts ⟨k, hk⟩
    have hbound : k ≤ 12 := by omega
    interval_cases k <;> norm_num [expectedCandidate, Polynomial.coeff_X, Polynomial.coeff_one] at hc ⊢ <;> exact hc
  · rw [countCoefficient_eq_zero_of_lt candidate (by omega)]
    simp [expectedCandidate, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, eq_comm,
      show k ≠ 0 by omega, show k ≠ 1 by omega,
      show k ≠ 2 by omega, show k ≠ 3 by omega, show k ≠ 4 by omega]

theorem comparator_finite_polynomial : finitePolynomial (J 12) = expectedComparator := by
  ext k
  rw [finitePolynomial_coeff]
  by_cases hk : k < 13
  · have hc := comparator_counts ⟨k, hk⟩
    have hbound : k ≤ 12 := by omega
    interval_cases k <;> norm_num [expectedComparator, Polynomial.coeff_X, Polynomial.coeff_one] at hc ⊢ <;> exact hc
  · rw [countCoefficient_eq_zero_of_lt (J 12) (by omega)]
    simp [expectedComparator, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one, eq_comm,
      show k ≠ 0 by omega, show k ≠ 1 by omega,
      show k ≠ 2 by omega, show k ≠ 3 by omega, show k ≠ 4 by omega]

theorem candidate_coefficients : A candidate = expectedCandidate :=
  (A_eq_finitePolynomial candidate candidate_coverage).trans candidate_finite_polynomial

theorem comparator_coefficients : A (J 12) = expectedComparator :=
  (A_eq_finitePolynomial (J 12) comparator_coverage).trans comparator_finite_polynomial
end BBPSplitStar
