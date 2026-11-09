import ABC.Unit

open MeasureTheory Filter Topology Pointwise InnerProductSpace Laplacian
open scoped RealInnerProductSpace

noncomputable section

namespace ABC

/-- The Laplacian of `x ↦ h (b • x)` is `b² (Δ h)(b • x)`. -/
private lemma laplacian_comp_smul {n : ℕ} (h : E n → ℝ) (hh : ContDiff ℝ 2 h) (b : ℝ)
    (x : E n) : Δ (fun z => h (b • z)) x = b ^ 2 * Δ h (b • x) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_comp_const_smul b hh, smul_apply, smul_eq_mul,
    Finset.mul_sum]

/-- Rescaling a pulsating front by `x ↦ b • x`, `t ↦ b² t`. -/
private lemma front_rescale {n : ℕ} (b : ℝ) (hb : 0 < b) (L L' : ℝ) (hL : b * L' = L)
    (V V' : E n → E n) (hV : ∀ x, V' x = V (b • x)) (f f' : ℝ → ℝ)
    (hf : ∀ s, f' s = b ^ 2 * f s) (A A' : ℝ) (hA : A' = b * A) (e : E n) (c c' : ℝ)
    (hc : c' = b * c) (T : ℝ → E n → ℝ) (hT : IsPulsatingFront L V f A e c T) :
    ∃ T', IsPulsatingFront L' V' f' A' e c' T' := by
  obtain ⟨⟨h01, hdt, hC2, hcont, hcontt, hcontx, hcontxx, heq⟩, U, hU, hper, hbot, htop⟩ := hT
  -- the time derivative
  have hderiv : ∀ t x, deriv (fun s => T (b ^ 2 * s) (b • x)) t =
      b ^ 2 * deriv (fun s => T s (b • x)) (b ^ 2 * t) := fun t x =>
    deriv_comp_mul_left (b ^ 2) (fun s => T s (b • x)) t
  -- the space derivative
  have hfd : ∀ t x, fderiv ℝ (fun z => T (b ^ 2 * t) (b • z)) x =
      b • fderiv ℝ (T (b ^ 2 * t)) (b • x) := fun t x =>
    fderiv_comp_smul (f := T (b ^ 2 * t)) b
  have hcm : Continuous (fun p : ℝ × E n => ((b ^ 2 * p.1, b • p.2) : ℝ × E n)) := by fun_prop
  refine ⟨fun t x => T (b ^ 2 * t) (b • x), ⟨fun t x => h01 _ _, fun x => ?_, fun t => ?_,
    ?_, ?_, ?_, ?_, fun t x => ?_⟩, fun s x => U (b * s) (b • x), fun t x => ?_, fun s i x => ?_,
    ?_, ?_⟩
  · exact (hdt (b • x)).comp (differentiable_id.const_mul _)
  · exact (hC2 _).comp (contDiff_const_smul b)
  · exact hcont.comp hcm
  · simp only [hderiv]
    exact continuous_const.mul (hcontt.comp hcm)
  · simp only [hfd]
    exact (hcontx.comp hcm).const_smul b
  · simp only [iteratedFDeriv_comp_const_smul b (hC2 _)]
    exact (hcontxx.comp hcm).const_smul (b ^ 2)
  · show deriv (fun s => T (b ^ 2 * s) (b • x)) t +
        A' * ⟪V' x, gradient (fun z => T (b ^ 2 * t) (b • z)) x⟫ =
        Δ (fun z => T (b ^ 2 * t) (b • z)) x + f' (T (b ^ 2 * t) (b • x))
    have hg : ∀ (h : E n → ℝ) (y z : E n), ⟪y, gradient h z⟫ = fderiv ℝ h z y := fun h y z => by
      rw [real_inner_comm]; simp [gradient]
    have h1 := heq (b ^ 2 * t) (b • x)
    rw [hg] at h1
    rw [hderiv, laplacian_comp_smul _ (hC2 _), hf, hV, hA, hg, hfd]
    simp only [smul_apply, smul_eq_mul]
    linear_combination b ^ 2 * h1
  · show T (b ^ 2 * t) (b • x) = U (b * (⟪x, e⟫ - c' * t)) (b • x)
    rw [hU, hc, real_inner_smul_left]
    congr 1
    ring
  · show U (b * s) (b • (x + L' • ev i)) = U (b * s) (b • x)
    rw [smul_add, smul_smul, hL, hper]
  · rw [Metric.tendstoUniformly_iff] at hbot ⊢
    intro ε hε
    exact ((tendsto_id.const_mul_atBot hb).eventually (hbot ε hε)).mono fun s hs x => hs _
  · rw [Metric.tendstoUniformly_iff] at htop ⊢
    intro ε hε
    exact ((tendsto_id.const_mul_atTop hb).eventually (htop ε hε)).mono fun s hs x => hs _

/-- Fronts of period `2π` for `(V, f, K)` correspond to fronts of period `1`
for `(u, (2π)²f, 2πK)` with speeds multiplied by `2π`. -/
theorem cstar_rescale (f : ℝ → ℝ) (e : E 3) (K : ℝ) :
    cstar (2 * Real.pi) abcField f e K =
      cstar 1 abcUnit (fun s => (2 * Real.pi) ^ 2 * f s) e (2 * Real.pi * K) / (2 * Real.pi) := by
  set a := 2 * Real.pi with ha_def
  have ha : 0 < a := by positivity
  have hset : {c | ∃ T, IsPulsatingFront 1 abcUnit (fun s => a ^ 2 * f s) (a * K) e c T} =
      a • {c | ∃ T, IsPulsatingFront a abcField f K e c T} := by
    ext c
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨T, hT⟩
      refine ⟨a⁻¹ * c, ?_, by simp [smul_eq_mul, ha.ne']⟩
      refine front_rescale a⁻¹ (inv_pos.2 ha) 1 a (by field_simp) abcUnit abcField
        (fun x => ?_) _ f (fun s => ?_) _ K (by field_simp) e c _ rfl T hT
      · simp [abcUnit, ← ha_def, smul_smul, ha.ne']
      · field_simp
    · rintro ⟨c₁, ⟨T, hT⟩, rfl⟩
      exact front_rescale a ha a 1 (mul_one a) abcField abcUnit (fun x => rfl) f _
        (fun s => rfl) K _ rfl e c₁ _ rfl T hT
  unfold cstar
  rw [hset, Real.sInf_smul_of_nonneg ha.le, smul_eq_mul, mul_div_cancel_left₀ _ ha.ne']

end ABC
