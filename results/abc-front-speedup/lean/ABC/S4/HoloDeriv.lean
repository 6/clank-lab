import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-! Several complex variables: a function that is complex-differentiable on an open set has a
complex-differentiable `fderiv` there, hence is `C^∞`. Pinned Mathlib has this only on `ℂ`
(`DifferentiableOn.contDiffOn`). Proof: Cauchy's formula on complex lines, differentiated under
the integral, with a Cauchy estimate as the dominating bound. -/

open Set Metric Filter Topology MeasureTheory
open scoped ContDiff

noncomputable section

namespace ABC.S4.HoloDeriv

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
theorem hasDerivAt_line {f : E → F} {y : E} (hf : DifferentiableAt ℂ f y) (u : E) :
    HasDerivAt (fun z : ℂ => f (y + z • u)) (fderiv ℂ f y u) 0 := by
  have h1 : HasDerivAt (fun z : ℂ => y + z • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const u).const_add y
  have hf' : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • u) := by simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt (0 : ℂ) h1

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- Cauchy estimate: `fderiv` is locally bounded. -/
theorem exists_bound_fderiv {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ δ > 0, ∃ K, ball x₀ δ ⊆ U ∧ ∀ y ∈ ball x₀ δ, ‖fderiv ℂ f y‖ ≤ K := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hc : ContinuousAt f x₀ := (hf.differentiableAt (hU.mem_nhds hx₀)).continuousAt
  obtain ⟨η, hη, hηf⟩ := Metric.continuousAt_iff.1 hc 1 one_pos
  set δ := min ε η / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have h2δ : 2 * δ = min ε η := by rw [hδdef]; ring
  have hδU : ball x₀ (2 * δ) ⊆ U :=
    (ball_subset_ball (by rw [h2δ]; exact min_le_left _ _)).trans hεU
  refine ⟨δ, hδ, (‖f x₀‖ + 1) / δ, (ball_subset_ball (by linarith)).trans hδU, ?_⟩
  intro y hy
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
  set r := δ / ‖u‖ with hr_def
  have hr : 0 < r := by positivity
  have hmem : ∀ z ∈ closedBall (0 : ℂ) r, y + z • u ∈ ball x₀ (2 * δ) := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    rw [mem_closedBall, dist_zero_right] at hz
    have h1 : ‖z • u‖ ≤ δ := by
      rw [norm_smul]
      calc ‖z‖ * ‖u‖ ≤ r * ‖u‖ := by gcongr
        _ = δ := by rw [hr_def]; field_simp
    have h2 : ‖y - x₀‖ < δ := by rwa [mem_ball, dist_eq_norm] at hy
    calc ‖y + z • u - x₀‖ = ‖(y - x₀) + z • u‖ := by congr 1; abel
      _ ≤ ‖y - x₀‖ + ‖z • u‖ := norm_add_le _ _
      _ < 2 * δ := by linarith
  have hd : DifferentiableOn ℂ (fun z : ℂ => f (y + z • u)) (closedBall 0 r) := by
    intro z hz
    have hzU : y + z • u ∈ U := hδU (hmem z hz)
    exact ((hf.differentiableAt (hU.mem_nhds hzU)).comp z
      ((differentiableAt_const _).add (differentiableAt_id.smul_const u))).differentiableWithinAt
  have hbd : ∀ z ∈ sphere (0 : ℂ) r, ‖f (y + z • u)‖ ≤ ‖f x₀‖ + 1 := by
    intro z hz
    have hd' : dist (y + z • u) x₀ < η :=
      lt_of_lt_of_le (hmem z (sphere_subset_closedBall hz)) (by rw [h2δ]; exact min_le_right _ _)
    have := hηf hd'
    rw [dist_eq_norm] at this
    calc ‖f (y + z • u)‖ = ‖(f (y + z • u) - f x₀) + f x₀‖ := by congr 1; abel
      _ ≤ ‖f (y + z • u) - f x₀‖ + ‖f x₀‖ := norm_add_le _ _
      _ ≤ ‖f x₀‖ + 1 := by linarith
  have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (hd.diffContOnCl_ball subset_rfl) hbd
  have hyU : y ∈ U := hδU (ball_subset_ball (by linarith) hy)
  rw [(hasDerivAt_line (hf.differentiableAt (hU.mem_nhds hyU)) u).deriv] at hest
  calc ‖fderiv ℂ f y u‖ ≤ (‖f x₀‖ + 1) / r := hest
    _ = (‖f x₀‖ + 1) / δ * ‖u‖ := by rw [hr_def]; field_simp

/-- Directional derivatives of a holomorphic function are holomorphic. -/
theorem differentiableAt_fderiv_apply {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x₀ : E} (hx₀ : x₀ ∈ U) (v : E) :
    DifferentiableAt ℂ (fun x => fderiv ℂ f x v) x₀ := by
  borelize E
  have := FiniteDimensional.complete ℂ F
  have : ProperSpace (E →L[ℂ] F) := FiniteDimensional.proper ℂ _
  have : SecondCountableTopology (E →L[ℂ] F) := secondCountable_of_proper
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [map_zero]; exact differentiableAt_const _
  obtain ⟨δ, hδ, K, hδU, hK⟩ := exists_bound_fderiv hU hf hx₀
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  set R := δ / (4 * ‖v‖) with hR_def
  have hR : 0 < R := by positivity
  have hRv : 2 * R * ‖v‖ = δ / 2 := by rw [hR_def]; field_simp; ring
  have hmem : ∀ x ∈ ball x₀ (δ / 2), ∀ z : ℂ, ‖z‖ < 2 * R → x + z • v ∈ ball x₀ δ := by
    intro x hx z hz
    rw [mem_ball, dist_eq_norm] at hx ⊢
    have : ‖z • v‖ < δ / 2 := by
      rw [norm_smul, ← hRv]; exact mul_lt_mul_of_pos_right hz hv'
    calc ‖x + z • v - x₀‖ = ‖(x - x₀) + z • v‖ := by congr 1; abel
      _ ≤ ‖x - x₀‖ + ‖z • v‖ := norm_add_le _ _
      _ < δ := by linarith
  have hdiffAt : ∀ y ∈ ball x₀ δ, DifferentiableAt ℂ f y :=
    fun y hy => hf.differentiableAt (hU.mem_nhds (hδU hy))
  have hcirc : ∀ θ : ℝ, ‖circleMap (0 : ℂ) R θ‖ < 2 * R := by
    intro θ; rw [norm_circleMap_zero, abs_of_pos hR]; linarith
  set c : ℝ → ℂ := fun θ => deriv (circleMap 0 R) θ * ((circleMap 0 R θ - 0) ^ 2)⁻¹ with hc_def
  have hc_cont : Continuous c := by
    simp only [hc_def, deriv_circleMap, sub_zero]
    exact ((continuous_circleMap 0 R).mul continuous_const).mul
      (((continuous_circleMap 0 R).pow 2).inv₀ fun θ => pow_ne_zero _ (circleMap_ne_center hR.ne'))
  have hc_norm : ∀ θ, ‖c θ‖ = R⁻¹ := by
    intro θ
    simp only [hc_def, deriv_circleMap, sub_zero, norm_mul, norm_inv, norm_pow,
      norm_circleMap_zero, abs_of_pos hR, Complex.norm_I]
    field_simp
  set G : E → ℝ → F := fun x θ => c θ • f (x + circleMap 0 R θ • v) with hG_def
  set G' : E → ℝ → E →L[ℂ] F := fun x θ => c θ • fderiv ℂ f (x + circleMap 0 R θ • v)
    with hG'_def
  have hGcont : ∀ x ∈ ball x₀ (δ / 2), Continuous (G x) := by
    intro x hx
    refine hc_cont.smul ?_
    have hcont : ContinuousOn f (ball x₀ δ) := fun y hy => (hdiffAt y hy).continuousAt.continuousWithinAt
    exact hcont.comp_continuous (continuous_const.add ((continuous_circleMap 0 R).smul continuous_const))
      fun θ => hmem x hx _ (hcirc θ)
  have hcauchy : ∀ x ∈ ball x₀ (δ / 2),
      fderiv ℂ f x v = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, G x θ := by
    intro x hx
    have hdiff : DifferentiableOn ℂ (fun z : ℂ => f (x + z • v)) (ball 0 (2 * R)) := by
      intro z hz
      rw [mem_ball, dist_zero_right] at hz
      exact ((hdiffAt _ (hmem x hx z hz)).comp z
        ((differentiableAt_const _).add (differentiableAt_id.smul_const v))).differentiableWithinAt
    have h := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      isOpen_ball (closedBall_subset_ball (by linarith)) hdiff (mem_ball_self hR)
    have hx' : x ∈ ball x₀ δ := ball_subset_ball (by linarith) hx
    rw [← (hasDerivAt_line (hdiffAt x hx') v).deriv, ← h]
    simp only [circleIntegral, hG_def, hc_def, smul_smul]
  have hF : HasFDerivAt (fun x => ∫ θ in (0 : ℝ)..2 * Real.pi, G x θ)
      (∫ θ in (0 : ℝ)..2 * Real.pi, G' x₀ θ) x₀ := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (bound := fun _ => R⁻¹ * K) (ball_mem_nhds x₀ (by linarith : 0 < δ / 2)) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [ball_mem_nhds x₀ (by linarith : 0 < δ / 2)] with x hx
      exact (hGcont x hx).aestronglyMeasurable
    · exact (hGcont x₀ (mem_ball_self (by linarith))).intervalIntegrable _ _
    · refine (hc_cont.aestronglyMeasurable).smul ?_
      exact ((measurable_fderiv ℂ f).comp (continuous_const.add
        ((continuous_circleMap 0 R).smul continuous_const)).measurable).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun θ _ x hx => ?_
      simp only [hG'_def, norm_smul, hc_norm]
      exact mul_le_mul_of_nonneg_left (hK _ (hmem x hx _ (hcirc θ))) (by positivity)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun θ _ x hx => ?_
      have hd := (hdiffAt _ (hmem x hx _ (hcirc θ))).hasFDerivAt
      have := (hd.comp x ((hasFDerivAt_id x).add_const (circleMap 0 R θ • v))).const_smul (c θ)
      exact this
  have heq : (fun x => fderiv ℂ f x v) =ᶠ[𝓝 x₀]
      fun x => (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, G x θ := by
    filter_upwards [ball_mem_nhds x₀ (by linarith : 0 < δ / 2)] with x hx
    exact hcauchy x hx
  exact (hF.differentiableAt.const_smul _).congr_of_eventuallyEq heq

theorem differentiableAt_fderiv {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    DifferentiableAt ℂ (fderiv ℂ f) x₀ := by
  set b := Module.finBasis ℂ E
  have key : fderiv ℂ f = fun x => ∑ i, ContinuousLinearMap.smulRightL ℂ E F
      (LinearMap.toContinuousLinearMap (b.coord i)) (fderiv ℂ f x (b i)) := by
    funext x
    ext y
    simp
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    simp [map_smul]
  rw [key]
  exact DifferentiableAt.fun_sum fun i _ =>
    (ContinuousLinearMap.differentiableAt _).comp x₀ (differentiableAt_fderiv_apply hU hf hx₀ _)

theorem differentiableOn_fderiv {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : DifferentiableOn ℂ (fderiv ℂ f) U :=
  fun _ hx => (differentiableAt_fderiv hU hf hx).differentiableWithinAt

theorem contDiffOn_nat (n : ℕ) : ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] {f : E → F} {U : Set E}, IsOpen U → DifferentiableOn ℂ f U →
    ContDiffOn ℂ n f U := by
  induction n with
  | zero => intro F _ _ _ f U _ hf; exact contDiffOn_zero.2 hf.continuousOn
  | succ n ih =>
    intro F _ _ _ f U hU hf
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨hf, by simp, ih hU (differentiableOn_fderiv hU hf)⟩

/-- Holomorphic on an open set ⇒ `C^∞` there. -/
theorem contDiffOn {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ ∞ f U :=
  contDiffOn_infty.2 fun n => contDiffOn_nat n hU hf

theorem contDiffAt {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : E} (hx : x ∈ U) : ContDiffAt ℂ ∞ f x :=
  (contDiffOn hU hf).contDiffAt (hU.mem_nhds hx)

end ABC.S4.HoloDeriv
