import Uniform5.CompositionThreeRaySpan

/-! The squared type-(iii) equation follows from actual Gram data. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

/-- Algebraic elimination in a three-ray basis, retaining every polynomial
root without assuming the unsquared geometric sign. -/
theorem typeIII_gram_polynomial {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Submodule ℝ E) (hS : Module.finrank ℝ S = 3)
    {h z₁ z₂ v W : E} {γ c₁ c₂ A : ℝ}
    (hm : h ∈ S) (h₁m : z₁ ∈ S) (h₂m : z₂ ∈ S) (hvm : v ∈ S)
    (hh : ‖h‖ = 1) (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1) (hv : ‖v‖ = 1)
    (hh₁ : ⟪h, z₁⟫ = 0) (hh₂ : ⟪h, z₂⟫ = 0)
    (hγ : ⟪z₁, z₂⟫ = γ) (hγ₁ : γ ≠ 1) (hγ₂ : γ ≠ -1)
    (hc₁ : ⟪z₁, v⟫ = c₁) (hc₂ : ⟪z₂, v⟫ = c₂)
    (hWh : ⟪h, W⟫ = A / 2) (hW₁ : ⟪z₁, W⟫ = 1 / 2)
    (hW₂ : ⟪z₂, W⟫ = 1 / 2) (hWv : ⟪v, W⟫ = 1 / 2) :
    A ^ 2 * (1 - γ ^ 2 - c₁ ^ 2 - c₂ ^ 2 + 2 * γ * c₁ * c₂) * (1 + γ) -
      (1 + γ - c₁ - c₂) ^ 2 * (1 - γ) = 0 := by
  rw [← three_ray_span S hS hm h₁m h₂m hh hz₁ hz₂ hh₁ hh₂
    (hγ ▸ hγ₁) (hγ ▸ hγ₂), Submodule.mem_span_insert] at hvm
  obtain ⟨η, u, hu, he⟩ := hvm
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
  have hh₁' : ⟪z₁, h⟫ = 0 := (real_inner_comm _ _).trans hh₁
  have hh₂' : ⟪z₂, h⟫ = 0 := (real_inner_comm _ _).trans hh₂
  have hγ' : ⟪z₂, z₁⟫ = γ := (real_inner_comm _ _).trans hγ
  have e₁ : α + β * γ = c₁ := by
    simpa [he, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      hz₁, hh₁', hγ] using hc₁
  have e₂ : α * γ + β = c₂ := by
    simpa [he, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      hz₂, hh₂', hγ'] using hc₂
  have ew : A * η = 1 - α - β := by
    rw [he, inner_add_left, real_inner_smul_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, hWh, hW₁, hW₂] at hWv
    linarith
  have en : η ^ 2 + α ^ 2 + β ^ 2 + 2 * α * β * γ = 1 := by
    have en := congrArg (fun x : E => ⟪x, x⟫) he
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hh, hz₁, hz₂, hv,
      hh₁, hh₂, hh₁', hh₂', hγ, hγ', one_pow, mul_zero, zero_add, add_zero,
      mul_one] at en
    simp only [norm_smul, Real.norm_eq_abs, hh, hz₁, hz₂, mul_one, sq_abs] at en
    nlinarith [en]
  have hN : 1 - γ ^ 2 - c₁ ^ 2 - c₂ ^ 2 + 2 * γ * c₁ * c₂ =
      (1 - γ ^ 2) * η ^ 2 := by
    rw [← e₁, ← e₂]
    calc
      _ = (1 - γ ^ 2) * (1 - α ^ 2 - β ^ 2 - 2 * α * β * γ) := by ring
      _ = _ := by congr 1; linarith
  have hM : 1 + γ - c₁ - c₂ = (1 + γ) * (A * η) := by
    rw [← e₁, ← e₂, ew]
    ring
  rw [hN, hM]
  ring

end Uniform5.Composition
