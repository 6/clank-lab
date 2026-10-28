import D5

namespace LNEDPilot
open Polynomial

/-- The source's two-sided Mathieu condition on a subset of Q[X]. -/
def TwoSidedMathieu (W : Set ℚ[X]) : Prop :=
  ∀ a : ℚ[X], (∀ m : ℕ, 1 ≤ m → a ^ m ∈ W) →
    ∀ b c : ℚ[X], ∃ N : ℕ, ∀ m : ℕ, N ≤ m → b * a ^ m * c ∈ W

/-- The literal Mathieu conclusion fails for the fixed ideal image. -/
theorem notMathieu_V : ¬ TwoSidedMathieu V := by
  intro hW
  obtain ⟨N, hN⟩ := hW (X ^ 2) endpoint_proved.2.2.1 X 1
  have hin := hN (max N 1) (le_max_left N 1)
  have hout := endpoint_proved.2.2.2 (max N 1) (le_max_right N 1)
  exact hout (by simpa only [mul_one] using hin)

/-- A concrete locally nilpotent Q-linear E-derivation sends a principal
ideal to a subset failing the source's two-sided Mathieu condition. -/
theorem exists_LNED_ideal_counterexample :
    ∃ (φ : ℚ[X] →ₐ[ℚ] ℚ[X]) (D : ℚ[X] →ₗ[ℚ] ℚ[X]) (J : Ideal ℚ[X]),
      (∀ h : ℚ[X], φ h = h.comp (X + 1)) ∧
      (∀ h : ℚ[X], D h = h - φ h) ∧
      J = Ideal.span {(X : ℚ[X]) * (X - C (1 / 2 : ℚ))} ∧
      (∀ h : ℚ[X], ∃ N : ℕ, 0 < N ∧ ((D : ℚ[X] → ℚ[X])^[N]) h = 0) ∧
      (∀ h k : ℚ[X], D (h * k) = D h * k + h * D k - D h * D k) ∧
      ¬ TwoSidedMathieu ((fun h : ℚ[X] => D h) '' (J : Set ℚ[X])) := by
  refine ⟨phiAlg, deltaLinear,
    Ideal.span {(X : ℚ[X]) * (X - C (1 / 2 : ℚ))}, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro h
    rfl
  · intro h
    rfl
  · intro h
    exact delta_locally_nilpotent h
  · intro h k
    exact delta_E h k
  · change ¬ TwoSidedMathieu
      (delta '' ((Ideal.span {(X : ℚ[X]) * (X - C (1 / 2 : ℚ))} : Ideal ℚ[X]) : Set ℚ[X]))
    rw [← I_eq_ideal]
    exact notMathieu_V

#print axioms notMathieu_V
#print axioms exists_LNED_ideal_counterexample
end LNEDPilot
