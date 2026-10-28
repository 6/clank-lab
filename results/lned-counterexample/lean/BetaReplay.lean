import Translate
import RootOne

open Polynomial LNEDPilot LNEDBeta

/-- Literal ideal-image statements for both signs, with no functional hypothesis. -/
theorem signed_half_literal : ∀ r : ℕ,
    ¬ TwoSidedMathieu (delta ''
      ((Ideal.span {(X : ℚ[X]) * (X - C ((r : ℚ) + 1 / 2))} : Ideal ℚ[X]) : Set ℚ[X])) ∧
    ¬ TwoSidedMathieu (delta ''
      ((Ideal.span {(X : ℚ[X]) * (X - C (-((r : ℚ) + 1 / 2)))} : Ideal ℚ[X]) : Set ℚ[X])) := by
  intro r
  exact ⟨all_positive_half_not_mathieu r, all_negative_half_not_mathieu r⟩

theorem signed_integer_literal : ∀ N : ℕ, 0 < N →
    TwoSidedMathieu (delta ''
      ((Ideal.span {(X : ℚ[X]) * (X - C (N : ℚ))} : Ideal ℚ[X]) : Set ℚ[X])) ∧
    TwoSidedMathieu (delta ''
      ((Ideal.span {(X : ℚ[X]) * (X - C (-(N : ℚ)))} : Ideal ℚ[X]) : Set ℚ[X])) := by
  intro N hN
  exact ⟨positive_integer_mathieu N hN, all_negative_integer_mathieu N hN⟩

example : ENDPOINT := endpoint_proved
example : ¬ rootOneENDPOINT := rootOne_altered_false
example : HalfWitnessEndpoint := half_witness_all
example (r : ℕ) := negative_half_witness r

#print axioms signed_half_literal
#print axioms signed_integer_literal
#print axioms LNEDBeta.half_witness_all
#print axioms LNEDBeta.negative_half_witness
#print axioms LNEDBeta.half_odd_moment_strict_sign
