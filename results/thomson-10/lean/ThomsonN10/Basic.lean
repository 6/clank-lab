import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Independent definitions for the N=10 Coulomb Thomson problem. -/

namespace ThomsonN10

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev Configuration := Fin 10 → R3

def IsSphereConfiguration (x : Configuration) : Prop :=
  (∀ i, ‖x i‖ = 1) ∧ Function.Injective x

noncomputable def coulombEnergy (x : Configuration) : ℝ :=
  ∑ i : Fin 10, ∑ j ∈ Finset.Ioi i, (‖x i - x j‖)⁻¹

def Congruent (x y : Configuration) : Prop :=
  ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (p : Equiv.Perm (Fin 10)), ∀ i, x i = g (y (p i))

noncomputable def vec (a b c : ℝ) : R3 := !₂[a, b, c]

theorem vec_norm_sq (a b c : ℝ) : ‖vec a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, vec, Fin.sum_univ_three]

theorem congruent_refl (x : Configuration) : Congruent x x := by
  exact ⟨LinearIsometryEquiv.refl ℝ R3, Equiv.refl _, fun _ => rfl⟩

end ThomsonN10
