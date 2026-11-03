import PathProbability

/-! Finite iid expectation and a bounded-variable lower-tail estimate. -/
namespace ADG
open Finset
open scoped Classical

noncomputable def matrixExpectation (m n : ℕ) (p : ℝ) (X : Matrix m n → ℝ) : ℝ :=
  ∑ A : Matrix m n, iidMass (columnMass m p) A * X A

lemma matrixMass_sum (m n : ℕ) (p : ℝ) :
    (∑ A : Matrix m n, iidMass (columnMass m p) A) = 1 := by
  simpa [matrixProb, iidProb] using matrixProb_univ m n p

lemma matrixExpectation_const (m n : ℕ) (p c : ℝ) :
    matrixExpectation m n p (fun _ => c) = c := by
  simp [matrixExpectation, ← Finset.sum_mul, matrixMass_sum]

lemma matrixExpectation_add (m n : ℕ) (p : ℝ) (X Y : Matrix m n → ℝ) :
    matrixExpectation m n p (fun A => X A+Y A) =
      matrixExpectation m n p X+matrixExpectation m n p Y := by
  simp [matrixExpectation, mul_add, Finset.sum_add_distrib]

lemma matrixExpectation_mul_const (m n : ℕ) (p c : ℝ) (X : Matrix m n → ℝ) :
    matrixExpectation m n p (fun A => c*X A) = c*matrixExpectation m n p X := by
  simp [matrixExpectation, ← Finset.mul_sum, mul_left_comm]

lemma matrixExpectation_sum {ι : Type} (m n : ℕ) (p : ℝ)
    (T : Finset ι) (X : ι → Matrix m n → ℝ) :
    matrixExpectation m n p (fun A => ∑ t ∈ T, X t A) =
      ∑ t ∈ T, matrixExpectation m n p (X t) := by
  simp only [matrixExpectation, Finset.mul_sum]
  exact Finset.sum_comm

lemma matrixExpectation_indicator (m n : ℕ) (p : ℝ) (E : Matrix m n → Prop) :
    matrixExpectation m n p (fun A => if E A then 1 else 0) = matrixProb m n p E := by
  classical
  unfold matrixExpectation matrixProb iidProb
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : E A <;> simp [h]

lemma matrixExpectation_mono (m n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    {X Y : Matrix m n → ℝ} (hXY : ∀ A, X A ≤ Y A) :
    matrixExpectation m n p X ≤ matrixExpectation m n p Y := by
  apply Finset.sum_le_sum
  intro A hA
  exact mul_le_mul_of_nonneg_left (hXY A)
    (iidMass_nonneg _ (columnMass_nonneg m p hp hp') A)

/-- Strong bounded-variable estimate, before any division by the upper bound. -/
theorem matrixExpectation_le_threshold_add_tail (m n : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (X : Matrix m n → ℝ)
    (M a : ℝ) (hX : ∀ A, 0 ≤ X A ∧ X A ≤ M) (ha : 0 ≤ a) :
    matrixExpectation m n p X ≤ a+M*matrixProb m n p (fun A => a ≤ X A) := by
  classical
  have hbound : ∀ A, X A ≤ a+M*(if a ≤ X A then 1 else 0) := by
    intro A
    by_cases h : a ≤ X A
    · simp only [h, if_true, mul_one]
      linarith [(hX A).2]
    · simp only [h, if_false, mul_zero, add_zero]
      exact le_of_lt (lt_of_not_ge h)
  have hh := matrixExpectation_mono m n p hp hp' hbound
  rw [matrixExpectation_add, matrixExpectation_const, matrixExpectation_mul_const,
    matrixExpectation_indicator] at hh
  exact hh

/-- A lower expectation and a deterministic bound force positive upper-tail probability. -/
theorem matrixProb_threshold_lower_bound (m n : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (X : Matrix m n → ℝ)
    (M a e : ℝ) (hM : 0 < M) (hX : ∀ A, 0 ≤ X A ∧ X A ≤ M)
    (ha : 0 ≤ a) (he : e ≤ matrixExpectation m n p X) :
    (e-a)/M ≤ matrixProb m n p (fun A => a ≤ X A) := by
  apply (div_le_iff₀ hM).mpr
  have h := matrixExpectation_le_threshold_add_tail m n p hp hp' X M a hX ha
  linarith

/-- Removing two bad events loses at most their two actual probabilities. -/
theorem matrixProb_inter_inter_lower_bound (m n : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (E H J : Matrix m n → Prop) :
    matrixProb m n p E-matrixProb m n p (fun A => ¬H A)-
      matrixProb m n p (fun A => ¬J A) ≤
      matrixProb m n p (fun A => E A ∧ H A ∧ J A) := by
  classical
  have hsum : matrixProb m n p E ≤
      matrixProb m n p (fun A => E A ∧ H A ∧ J A)+
      matrixProb m n p (fun A => ¬H A)+matrixProb m n p (fun A => ¬J A) := by
    unfold matrixProb iidProb
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro A hA
    have hμ := iidMass_nonneg (columnMass m p) (columnMass_nonneg m p hp hp') A
    by_cases he : E A <;> by_cases hh : H A <;> by_cases hj : J A <;>
      simp [he, hh, hj] <;> linarith
  linarith

theorem matrixProb_joint_good_lower_bound (m n : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (E : Matrix m n → Prop) :
    matrixProb m n p E-matrixProb m n p (fun A => ¬noLargeColumns A)-
      matrixProb m n p (fun A => ¬allExactPairs A) ≤
      matrixProb m n p (fun A => E A ∧ noLargeColumns A ∧ allExactPairs A) :=
  matrixProb_inter_inter_lower_bound m n p hp hp' E noLargeColumns allExactPairs

end ADG
