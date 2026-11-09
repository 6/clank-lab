import ABC.DriftAvg
import ABC.Unit

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ABC

/-- The cyclic coordinate shift `(σₖ v) i = v (i + k)`. -/
private def cyc (k : Fin 3) : E 3 ≃ₗᵢ[ℝ] E 3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.addRight k).symm

private lemma cyc_apply (k : Fin 3) (v : E 3) (i : Fin 3) : cyc k v i = v (i + k) := by
  simp [cyc, LinearIsometryEquiv.piLpCongrLeft_apply]

private lemma abcField_cyc (k : Fin 3) (ξ : E 3) : abcField (cyc k ξ) = cyc k (abcField ξ) := by
  ext i
  fin_cases k <;> fin_cases i <;> simp [cyc_apply, abcField]

private lemma measurableSet_cell (L : ℝ) : MeasurableSet (cell 3 L) := by
  have : cell 3 L = ⋂ i, (fun x : E 3 => x i) ⁻¹' Set.Ico 0 L := by
    ext x; simp [cell]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_Ico.preimage (by fun_prop)

private lemma inner_gradient_comp (W : E 3 → ℝ) (L : E 3 ≃L[ℝ] E 3) (x u : E 3) :
    ⟪u, gradient (fun y => W (L y)) x⟫ = ⟪gradient W (L x), L u⟫ := by
  rw [real_inner_comm, gradient, gradient, InnerProductSpace.toDual_symm_apply,
    InnerProductSpace.toDual_symm_apply]
  have := L.comp_right_fderiv (f := W) (x := x)
  simp only [Function.comp_def] at this
  rw [this]
  rfl

/-- `L x = σₖ (a • x)`. -/
private def cycSmul (k : Fin 3) {a : ℝ} (ha : a ≠ 0) : E 3 ≃L[ℝ] E 3 :=
  ((LinearEquiv.smulOfNeZero ℝ (E 3) a ha).trans (cyc k).toLinearEquiv).toContinuousLinearEquiv

private lemma cycSmul_apply (k : Fin 3) {a : ℝ} (ha : a ≠ 0) (x : E 3) :
    cycSmul k ha x = cyc k (a • x) := rfl

private lemma mem_cell_cycSmul (k : Fin 3) {a : ℝ} (ha : 0 < a) (x : E 3) :
    cycSmul k ha.ne' x ∈ cell 3 a ↔ x ∈ cell 3 1 := by
  simp only [cell, Set.mem_ofPred_eq, cycSmul_apply, cyc_apply, PiLp.smul_apply, smul_eq_mul,
    Set.mem_Ico]
  have key : ∀ t : ℝ, (0 ≤ a * t ∧ a * t < a) ↔ (0 ≤ t ∧ t < 1) := fun t => by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨nonneg_of_mul_nonneg_right (by linarith) ha, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by positivity, by nlinarith⟩
  simp only [key]
  exact ⟨fun h i => by simpa using h (i - k), fun h i => h _⟩

private lemma image_cycSmul (k : Fin 3) {a : ℝ} (ha : 0 < a) :
    cycSmul k ha.ne' '' cell 3 1 = cell 3 a := by
  rw [ContinuousLinearEquiv.image_eq_preimage_symm]
  ext y
  rw [Set.mem_preimage, ← mem_cell_cycSmul k ha, ContinuousLinearEquiv.apply_symm_apply]

private lemma cell_subset_closedBall {L : ℝ} (hL : 0 < L) :
    cell 3 L ⊆ Metric.closedBall (0 : E 3) (3 * L) := by
  intro x hx
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h := fun i => hx i
  simp only [Set.mem_Ico] at h
  simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three]
  nlinarith [h 0, h 1, h 2]

private lemma integrableOn_cell {f : E 3 → ℝ} (hf : Continuous f) {L : ℝ} (hL : 0 < L) :
    IntegrableOn f (cell 3 L) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 (3 * L))).mono_set
    (cell_subset_closedBall hL)

private lemma continuous_abcField_apply (i : Fin 3) : Continuous fun x : E 3 => abcField x i := by
  fin_cases i <;> simp [abcField] <;> fun_prop

private lemma integral_inner_abcField {W : E 3 → ℝ} (hW : Continuous W) {L : ℝ} (hL : 0 < L)
    (f : E 3) :
    ∫ x in cell 3 L, ⟪abcField x, f⟫ * W x =
      f 0 * (∫ x in cell 3 L, abcField x 0 * W x) + f 1 * (∫ x in cell 3 L, abcField x 1 * W x) +
        f 2 * ∫ x in cell 3 L, abcField x 2 * W x := by
  have hi : ∀ i, IntegrableOn (fun x => abcField x i * W x) (cell 3 L) := fun i =>
    integrableOn_cell ((continuous_abcField_apply i).mul hW) hL
  have : ∀ x, ⟪abcField x, f⟫ * W x =
      f 0 * (abcField x 0 * W x) + f 1 * (abcField x 1 * W x) + f 2 * (abcField x 2 * W x) := by
    intro x
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
    ring
  simp_rw [this]
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
  all_goals first
    | exact (hi 0).const_mul _
    | exact (hi 1).const_mul _
    | exact (hi 2).const_mul _
    | exact ((hi 0).const_mul _).add ((hi 1).const_mul _)

/-- For every unit `e`, a first integral (a tube, or a cyclic copy of it)
with nonzero drift along `e`, rescaled to period `1`. -/
theorem drift_unit {W : E 3 → ℝ} (hW : VortexTube W) (e : E 3) (he : ‖e‖ = 1) :
    ∃ (w : E 3 → ℝ) (C : NNReal), LipschitzWith C w ∧ Periodic 1 w ∧
      (∀ᵐ x, ⟪abcUnit x, gradient w x⟫ = 0) ∧ ∫ x in cell 3 1, ⟪abcUnit x, e⟫ * w x ≠ 0 := by
  have havg := tube_averages hW
  obtain ⟨⟨C, hC⟩, hper, -, -, hae, -⟩ := hW
  have ha : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨j, hj⟩ : ∃ j, e j ≠ 0 := by
    by_contra! h
    have : e = 0 := by ext i; simp [h i]
    simp [this] at he
  set k : Fin 3 := j - 2 with hk
  set L := cycSmul k ha.ne' with hL
  have hek : cyc k e 2 = e j := by rw [cyc_apply, hk, add_sub_cancel]
  refine ⟨fun x => W (L x), C * ‖(L : E 3 →L[ℝ] E 3)‖₊, hC.comp L.lipschitzWith, ?_, ?_, ?_⟩
  · intro i x
    have hLe : L (ev i) = (2 * Real.pi) • ev (i - k) := by
      ext m
      simp only [hL, cycSmul_apply, cyc_apply, PiLp.smul_apply, smul_eq_mul,
        PiLp.single_apply, eq_sub_iff_add_eq]
    simp only [one_smul, map_add, hLe]
    exact hper (i - k) (L x)
  · have hdet : (L : E 3 →L[ℝ] E 3).det ≠ 0 := L.toLinearEquiv.isUnit_det'.ne_zero
    have hq := Measure.ContinuousLinearMap.quasiMeasurePreserving (μ := volume)
      (L : E 3 →L[ℝ] E 3) hdet
    filter_upwards [hq.ae hae] with x hx
    rw [inner_gradient_comp]
    have : L (abcUnit x) = (2 * Real.pi) • abcField (L x) := by
      rw [hL, cycSmul_apply, cycSmul_apply, abcUnit, abcField_cyc, map_smul]
    rw [this, inner_smul_right, real_inner_comm]
    exact mul_eq_zero_of_right _ hx
  · set g : E 3 → ℝ := fun η => ⟪abcField η, cyc k e⟫ * W η
    have hint : ∀ x, ⟪abcUnit x, e⟫ * W (L x) = g (L x) := by
      intro x
      simp only [g, hL, cycSmul_apply, abcField_cyc, LinearIsometryEquiv.inner_map_map, abcUnit]
    simp_rw [hint]
    have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_cell 1)
      (fun x _ => (L : E 3 →L[ℝ] E 3).hasFDerivWithinAt) L.injective.injOn g
    simp only [ContinuousLinearEquiv.coe_coe] at hcov
    rw [image_cycSmul k ha, integral_smul] at hcov
    rw [integral_inner_abcField hC.continuous ha, havg.1, havg.2.1, hek] at hcov
    intro h0
    rw [h0, smul_zero] at hcov
    have : e j * ∫ x in cell 3 (2 * Real.pi), abcField x 2 * W x ≠ 0 :=
      mul_ne_zero hj havg.2.2.ne'
    exact this (by simpa using hcov)

end ABC
