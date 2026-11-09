import ABC.S4.R3Aux0

/-! R3 auxiliaries: holomorphic dependence of integrals on a parameter. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real MeasureTheory

noncomputable section

namespace ABC.S4.R3Aux

open ABC.S4

/-- Differentiation under the integral sign for a holomorphic parameter. -/
theorem hasDerivAt_intervalIntegral_of_holo {φ : ℝ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn (fun p : ℝ × ℂ => φ p.1 p.2) (Icc a b ×ˢ U))
    (hd : ∀ θ ∈ Icc a b, DifferentiableOn ℂ (φ θ) U) {t : ℂ} (ht : t ∈ U) :
    HasDerivAt (fun t => ∫ θ in a..b, φ θ t) (∫ θ in a..b, deriv (φ θ) t) t := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU t ht
  set δ := ε / 3 with hδ
  have hδ0 : 0 < δ := by positivity
  have hcb : closedBall t (2 * δ) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  have hK : IsCompact (Icc a b ×ˢ closedBall t (2 * δ)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hc.mono (prod_mono subset_rfl hcb))
  have hΙ : uIoc a b ⊆ Icc a b := by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self
  have hcont : ∀ z ∈ U, ContinuousOn (fun θ => φ θ z) (Icc a b) := fun z hz =>
    hc.comp (Continuous.continuousOn (f := fun θ : ℝ => (θ, z)) (by fun_prop)) (fun θ hθ => ⟨hθ, hz⟩)
  have hball : ball t δ ⊆ U := (ball_subset_ball (by linarith)).trans hεU
  have hderiv : ∀ θ ∈ Icc a b, ∀ x ∈ ball t δ, HasDerivAt (φ θ) (deriv (φ θ) x) x :=
    fun θ hθ x hx => ((hd θ hθ).differentiableAt (hU.mem_nhds (hball hx))).hasDerivAt
  have hbound : ∀ θ ∈ Icc a b, ∀ x ∈ ball t δ, ‖deriv (φ θ) x‖ ≤ M / δ := by
    intro θ hθ x hx
    have hsub : closedBall x δ ⊆ closedBall t (2 * δ) := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      rw [mem_ball] at hx
      linarith [dist_triangle z x t]
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ0
    · apply DifferentiableOn.diffContOnCl
      rw [closure_ball x hδ0.ne']
      exact (hd θ hθ).mono (hsub.trans hcb)
    · intro z hz
      exact hM (θ, z) ⟨hθ, hsub (sphere_subset_closedBall hz)⟩
  have hmeas : AEStronglyMeasurable (fun θ => deriv (φ θ) t) (volume.restrict (uIoc a b)) := by
    set h : ℕ → ℂ := fun n => ((δ / n : ℝ) : ℂ) with hh
    have hhU : ∀ n, t + h n ∈ U := by
      intro n
      apply hcb
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hh]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp; positivity
      · rw [div_le_iff₀ (by exact_mod_cast h0)]
        have : (1 : ℝ) ≤ n := by exact_mod_cast h0
        nlinarith
    have hlim : Tendsto h atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have := (Complex.continuous_ofReal.tendsto 0).comp
          (tendsto_const_div_atTop_nhds_zero_nat δ)
        exact this
      · filter_upwards [eventually_ge_atTop 1] with n hn
        simp only [hh, mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
        have : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n θ => (h n)⁻¹ • (φ θ (t + h n) - φ θ t)) (fun n => ?_) ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      exact (((hcont _ (hhU n)).sub (hcont _ ht)).const_smul (h n)⁻¹).mono hΙ
    · refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun θ hθ => ?_)
      exact (hasDerivAt_iff_tendsto_slope_zero.1
        (hderiv θ (hΙ hθ) t (mem_ball_self hδ0))).comp hlim
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x θ => φ θ x) (F' := fun x θ => deriv (φ θ) x) (bound := fun _ => M / δ)
    (ball_mem_nhds t hδ0) ?_ ?_ hmeas ?_ intervalIntegrable_const ?_).2
  · filter_upwards [ball_mem_nhds t hδ0] with x hx
    exact ((hcont x (hball hx)).mono hΙ).aestronglyMeasurable measurableSet_uIoc
  · exact ((hcont t ht).mono (by rw [uIcc_of_le hab])).intervalIntegrable
  · exact Eventually.of_forall fun θ hθ x hx => hbound θ (hΙ hθ) x hx
  · exact Eventually.of_forall fun θ hθ x hx => hderiv θ (hΙ hθ) x hx

/-- A circle integral of a jointly continuous, parameter-holomorphic integrand is holomorphic. -/
theorem differentiableOn_circleIntegral_of_holo {φ : ℂ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn (fun p : ℂ × ℂ => φ p.1 p.2) (sphere c r ×ˢ U))
    (hd : ∀ ζ ∈ sphere c r, DifferentiableOn ℂ (φ ζ) U) :
    DifferentiableOn ℂ (fun p => ∮ ζ in C(c, r), φ ζ p) U := by
  intro p hp
  have hcm : ∀ θ : ℝ, circleMap c r θ ∈ sphere c r := fun θ => circleMap_mem_sphere c hr.le θ
  have h := hasDerivAt_intervalIntegral_of_holo
    (φ := fun θ z => deriv (circleMap c r) θ • φ (circleMap c r θ) z) hU
    (by positivity : (0:ℝ) ≤ 2 * π) ?_ ?_ hp
  · exact h.differentiableAt.differentiableWithinAt
  · simp only [deriv_circleMap]
    refine ContinuousOn.smul (f := fun p : ℝ × ℂ => circleMap 0 r p.1 * Complex.I)
      (g := fun p : ℝ × ℂ => φ (circleMap c r p.1) p.2)
      (Continuous.continuousOn (by fun_prop)) ?_
    exact hc.comp (Continuous.continuousOn
      (f := fun x : ℝ × ℂ => (circleMap c r x.1, x.2)) (by fun_prop))
      (fun x hx => ⟨hcm x.1, hx.2⟩)
  · intro θ _
    exact (differentiableOn_const (s := U) (deriv (circleMap c r) θ)).smul (hd _ (hcm θ))

/-- A circle integral of a jointly continuous integrand is continuous in the parameter. -/
theorem continuousOn_circleIntegral_param {φ : ℂ → ℂ × ℂ → ℂ} {V : Set (ℂ × ℂ)} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hc : ContinuousOn (fun p : ℂ × (ℂ × ℂ) => φ p.1 p.2) (sphere c r ×ˢ V)) :
    ContinuousOn (fun p => ∮ ζ in C(c, r), φ ζ p) V := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hcm : ∀ θ : ℝ, circleMap c r θ ∈ sphere c r := fun θ => circleMap_mem_sphere c hr.le θ
  show Continuous fun x : V =>
    ∫ θ in (0:ℝ)..2 * π, deriv (circleMap c r) θ • φ (circleMap c r θ) x.1
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  simp only [deriv_circleMap]
  rw [continuousOn_iff_continuous_domRestrict] at hc
  have : Continuous fun q : V × ℝ => φ (circleMap c r q.2) q.1.1 :=
    hc.comp (f := fun q : V × ℝ =>
      (⟨(circleMap c r q.2, q.1.1), hcm q.2, q.1.2⟩ : sphere c r ×ˢ V)) (by fun_prop)
  exact (by fun_prop : Continuous fun q : V × ℝ => circleMap 0 r q.2 * Complex.I).smul this

end ABC.S4.R3Aux
