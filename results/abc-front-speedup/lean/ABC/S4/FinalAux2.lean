import Mathlib

open Set Metric Filter Topology Real

noncomputable section

namespace ABC.S4.FinalAux

theorem circle_inv {Θ : ℝ → ℝ} (hc : Continuous Θ) {κ : ℝ} (hκ : κ ≤ 1 / 2)
    (hl : ∀ a b, |(Θ a - a) - (Θ b - b)| ≤ κ * |a - b|) :
    Function.Surjective Θ ∧ ∀ a b, |a - b| ≤ 2 * |Θ a - Θ b| := by
  have key : ∀ a b, |a - b| ≤ 2 * |Θ a - Θ b| := by
    intro a b
    have h1 := hl a b
    have h2 : |a - b| - |Θ a - Θ b| ≤ |(Θ a - a) - (Θ b - b)| := by
      have := abs_sub_abs_le_abs_sub (a - b) (Θ a - Θ b)
      have e : (a - b) - (Θ a - Θ b) = -((Θ a - a) - (Θ b - b)) := by ring
      rw [e, abs_neg] at this
      exact this
    have h3 : κ * |a - b| ≤ 1 / 2 * |a - b| :=
      mul_le_mul_of_nonneg_right hκ (abs_nonneg _)
    linarith
  refine ⟨?_, key⟩
  intro y
  set X := 2 * |y - Θ 0| with hX
  have hX0 : 0 ≤ X := by positivity
  have hpos : y ≤ Θ X := by
    have h1 := hl X 0
    have h1' := (abs_le.mp h1).1
    simp only [sub_zero, abs_of_nonneg hX0] at h1'
    have h3 : κ * X ≤ 1 / 2 * X := mul_le_mul_of_nonneg_right hκ hX0
    have h4 : y - Θ 0 ≤ |y - Θ 0| := le_abs_self _
    linarith
  have hneg : Θ (-X) ≤ y := by
    have h1 := hl (-X) 0
    have h1' := (abs_le.mp h1).2
    simp only [sub_zero, abs_neg, abs_of_nonneg hX0] at h1'
    have h3 : κ * X ≤ 1 / 2 * X := mul_le_mul_of_nonneg_right hκ hX0
    have h4 : -(y - Θ 0) ≤ |y - Θ 0| := neg_le_abs _
    linarith
  obtain ⟨x, hx⟩ := intermediate_value_univ (-X) X hc ⟨hneg, hpos⟩
  exact ⟨x, hx⟩

end ABC.S4.FinalAux
