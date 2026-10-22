import Mathlib

namespace OAI

/-! # The centered support projections in the contracting local kernel -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def finiteSupportMean {α : Type*} (S : Finset α) (f : α → ℂ) : ℂ :=
  (S.card : ℂ)⁻¹ * ∑ x ∈ S, f x

noncomputable def centeredSupportProjection {α : Type*}
    (S : Finset α) (f : α → ℂ) (x : α) : ℂ :=
  if x ∈ S then f x - finiteSupportMean S f else 0

theorem finiteSupportMean_spec {α : Type*} (S : Finset α) (f : α → ℂ) :
    (S.card : ℂ) * finiteSupportMean S f = ∑ x ∈ S, f x := by
  by_cases hs : S.card = 0
  · have he : S = ∅ := Finset.card_eq_zero.mp hs
    simp [he, finiteSupportMean]
  · unfold finiteSupportMean
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]

end Ostmann

end OAI
