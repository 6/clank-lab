import ABC.TubeProofAux3

/-!
# Auxiliary facts for the tube construction: first integral and the box condition
-/

open Set Metric Real MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace ABC

/-- A Lipschitz function constant along orbits satisfies `V·∇W = 0` almost everywhere
(Rademacher and the chain rule along the orbit through each point of differentiability). -/
lemma ae_inner_gradient_eq_zero {W : E 3 → ℝ} {C : NNReal} (hL : LipschitzWith C W)
    (hinv : ∀ ξ t, W (Γ ξ t) = W ξ) : ∀ᵐ x, ⟪abcField x, gradient W x⟫ = 0 := by
  filter_upwards [hL.ae_differentiableAt (μ := volume)] with x hx
  have hf : HasFDerivAt W (fderiv ℝ W x) (Γ x 0) := by rw [Γ_zero]; exact hx.hasFDerivAt
  have h1 := hf.comp_hasDerivAt 0 (Γ_orbit x 0)
  rw [Γ_zero] at h1
  have h2 : HasDerivAt (W ∘ Γ x) 0 0 := by
    have : W ∘ Γ x = fun _ => W x := funext fun t => hinv x t
    rw [this]; exact hasDerivAt_const _ _
  have := h1.unique h2
  rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]
  exact this

lemma box_x {u : ℝ} (h : 0 < Real.cos u) :
    ∃ m : ℤ, u ∈ Icc (-π + 2 * π * m + 1) (-π + 2 * π * (m + 1) - 1) := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  set m := toIcoDiv h2π (-π) u
  have hm := sub_toIcoDiv_zsmul_mem_Ico h2π (-π) u
  rw [zsmul_eq_mul] at hm
  set y := u - (m : ℝ) * (2 * π) with hy
  have hcy : Real.cos y = Real.cos u := by
    rw [hy]; exact Real.cos_sub_int_mul_two_pi u m
  have hpi := Real.pi_gt_three
  refine ⟨m, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have : Real.cos (-y) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [hm.1])
    rw [Real.cos_neg, hcy] at this
    linarith
  · by_contra hlt
    push Not at hlt
    have : Real.cos y ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [hm.2])
    rw [hcy] at this
    linarith

lemma box_y {u : ℝ} (h : 0 < Real.sin u) :
    ∃ k : ℤ, u ∈ Icc (-(π / 2) + 2 * π * k + 1) (-(π / 2) + 2 * π * (k + 1) - 1) := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  set k := toIcoDiv h2π (-(π / 2)) u
  have hk := sub_toIcoDiv_zsmul_mem_Ico h2π (-(π / 2)) u
  rw [zsmul_eq_mul] at hk
  set y := u - (k : ℝ) * (2 * π) with hy
  have hsy : Real.sin y = Real.sin u := by
    rw [hy]; exact Real.sin_sub_int_mul_two_pi u k
  have hpi := Real.pi_gt_three
  refine ⟨k, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have : Real.sin y < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [hk.1])
    rw [hsy] at this
    linarith
  · by_contra hlt
    push Not at hlt
    have : Real.sin (y - 2 * π) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hk.2]) (by linarith)
    rw [Real.sin_sub_two_pi, hsy] at this
    linarith

lemma box_of_Vz {x : E 3} (h : 19 / 10 ≤ abcField x 2) : ∃ m k : ℤ,
    x 0 ∈ Icc (-π + 2 * π * m + 1) (-π + 2 * π * (m + 1) - 1) ∧
    x 1 ∈ Icc (-(π / 2) + 2 * π * k + 1) (-(π / 2) + 2 * π * (k + 1) - 1) := by
  rw [abcField_apply_two] at h
  have h1 := Real.sin_le_one (x 1)
  have h2 := Real.cos_le_one (x 0)
  obtain ⟨m, hm⟩ := box_x (u := x 0) (by linarith)
  obtain ⟨k, hk⟩ := box_y (u := x 1) (by linarith)
  exact ⟨m, k, hm, hk⟩

end ABC
