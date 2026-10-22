import Mathlib

namespace OAI

/-! # Linear evaluation of the finite kernel against two fixed vectors -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def kernelPairingLinearMap {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) : (α → β → ℂ) →ₗ[ℂ] ℂ where
  toFun M := ∑ x, conj (f x) * ∑ y, M x y * g y
  map_add' M N := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c M := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring

end Ostmann

end OAI
