import PathCounting
import BadMiddleBound
import QuantitativeProbability

/-! Expected number of bad middles under the finite iid law. -/
namespace ADG
open Finset
open scoped Classical

lemma orderedPathCount_cast {m n : ℕ} (A : Matrix m n) :
    (orderedPathCount A : ℝ) = ∑ t : PathTuple m, if pathOccurs A t then 1 else 0 := by
  unfold orderedPathCount
  rw [card_eq_sum_ones, sum_filter]
  push_cast
  rfl

theorem expected_bad_middles_identity (m n : ℕ) (p : ℝ) :
    8 * matrixExpectation m n p (fun A => (B A : ℝ)) =
      ∑ t : PathTuple m, matrixProb m n p (fun A => pathOccurs A t) := by
  rw [← matrixExpectation_mul_const]
  have he : (fun A : Matrix m n => (8 : ℝ)*(B A : ℝ)) =
      (fun A => ∑ t : PathTuple m, if pathOccurs A t then (1 : ℝ) else 0) := by
    funext A
    rw [← orderedPathCount_cast]
    exact_mod_cast (orderedPathCount_eq_eight_B A).symm
  rw [he,matrixExpectation_sum]
  simp_rw [matrixExpectation_indicator]

/-- Explicit rational retained for the complete positive-probability construction. -/
def badDensity : ℚ := 1/(196608*10^9)

lemma badDensity_pos : 0 < badDensity := by norm_num [badDensity]

theorem expected_bad_middles_lower {k : ℕ} (hk : 14 ≤ k) :
    (badDensity : ℝ)*(k : ℝ) ≤
      matrixExpectation k (k^10) (parameterP k) (fun A => (B A : ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hsum : (Fintype.card (PathTuple k) : ℝ) *
      (1/(192*10^9*(k : ℝ)^6)) ≤
      ∑ t : PathTuple k, matrixProb k (k^10) (parameterP k) (fun A => pathOccurs A t) := by
    calc
      _ = ∑ _t : PathTuple k, (1/(192*10^9*(k : ℝ)^6)) := by simp
      _ ≤ _ := sum_le_sum (fun t _ => parameter_path_probability_lower hk t)
  have hrows := pathTuple_card_ge hk
  have hnonneg : 0 ≤ (1/(192*10^9*(k : ℝ)^6) : ℝ) := by positivity
  have hlower := (mul_le_mul_of_nonneg_right hrows hnonneg).trans hsum
  rw [← expected_bad_middles_identity] at hlower
  have he : ((k : ℝ)^7/128)*(1/(192*10^9*(k : ℝ)^6)) =
      8*(badDensity : ℝ)*(k : ℝ) := by
    norm_num [badDensity]
    field_simp
    <;> ring
  rw [he] at hlower
  linarith

end ADG
