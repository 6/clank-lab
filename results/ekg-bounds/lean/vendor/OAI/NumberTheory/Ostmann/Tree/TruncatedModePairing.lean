import Mathlib

namespace OAI

/-! # Pairing the truncated kernel against only its active centered modes -/

namespace Ostmann
open WithLp
open scoped Classical BigOperators ComplexConjugate

noncomputable def countingVectorNorm {α : Type*} [Fintype α] (f : α → ℂ) : ℝ :=
  ‖(toLp 2 f : EuclideanSpace ℂ α)‖

theorem countingVectorNorm_sq {α : Type*} [Fintype α] (f : α → ℂ) :
    countingVectorNorm f ^ 2 = ∑ x, ‖f x‖ ^ 2 := EuclideanSpace.norm_sq_eq _

end Ostmann

end OAI
