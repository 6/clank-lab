import Mathlib
import OAI.NumberTheory.Ostmann.Supply.CenteredSupportProjection

namespace OAI

/-! # Literal residue-point coordinates of the local kernel matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def residuePointVector {p : ℕ} (a x : ZMod p) : ℂ :=
  if x = a then 1 else 0

theorem centeredSupportProjection_sum {α : Type*}
    (S : Finset α) (f : α → ℂ) :
    (∑ x ∈ S, centeredSupportProjection S f x) = 0 := by
  have he : (∑ x ∈ S, centeredSupportProjection S f x) =
      (∑ x ∈ S, f x) - (S.card : ℂ) * finiteSupportMean S f := by
    simp only [centeredSupportProjection]
    rw [Finset.sum_congr rfl (fun x hx => ite_eq_left hx), Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [he, finiteSupportMean_spec, sub_self]

theorem centeredSupportProjection_idempotent {α : Type*}
    (S : Finset α) (f : α → ℂ) :
    centeredSupportProjection S (centeredSupportProjection S f) = centeredSupportProjection S f := by
  have hm : finiteSupportMean S (centeredSupportProjection S f) = 0 := by
    rw [finiteSupportMean, centeredSupportProjection_sum, mul_zero]
  funext x
  by_cases hx : x ∈ S
  · simp only [centeredSupportProjection, ite_eq_left hx, hm, sub_zero]
  · simp only [centeredSupportProjection, ite_eq_right hx]

end Ostmann

end OAI
