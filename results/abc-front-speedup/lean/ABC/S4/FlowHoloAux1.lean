import Mathlib

/-! L0a helper: a uniform limit of ℂ-differentiable maps between complex normed spaces is
ℂ-differentiable (several variables; Mathlib's `TendstoLocallyUniformlyOn.differentiableOn` has
domain `ℂ`). Proof: one-variable Cauchy estimates along complex lines make the derivatives
uniformly Cauchy, then `hasFDerivAt_of_tendstoUniformlyOn`. -/

open Set Metric Filter Topology

noncomputable section

namespace ABC.S4.FlowHoloAux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- Cauchy estimate for the Fréchet derivative, via complex lines. -/
theorem norm_fderiv_le_of_closedBall {h : E → F} {s : Set E} (hs : IsOpen s)
    (hh : DifferentiableOn ℂ h s) {y : E} {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hsub : closedBall y ρ ⊆ s) (hb : ∀ z ∈ closedBall y ρ, ‖h z‖ ≤ C) :
    ‖fderiv ℂ h y‖ ≤ C / ρ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hC hρ.le) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set R : ℝ := ρ / ‖v‖ with hRdef
  have hR : 0 < R := div_pos hρ hnv
  let φ : ℂ → F := fun z => h (y + z • v)
  have hmem : ∀ z ∈ closedBall (0 : ℂ) R, y + z • v ∈ closedBall y ρ := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    rw [mem_closedBall, dist_zero_right] at hz
    calc ‖z‖ * ‖v‖ ≤ R * ‖v‖ := by gcongr
      _ = ρ := by rw [hRdef]; field_simp
  have hdiff : ∀ z ∈ closedBall (0 : ℂ) R, HasDerivAt φ (fderiv ℂ h (y + z • v) v) z := by
    intro z hz
    have hd : DifferentiableAt ℂ h (y + z • v) :=
      hh.differentiableAt (hs.mem_nhds (hsub (hmem z hz)))
    have hl : HasDerivAt (fun w : ℂ => y + w • v) v z := by
      simpa using ((hasDerivAt_id z).smul_const v).const_add y
    exact hd.hasFDerivAt.comp_hasDerivAt z hl
  have hdc : DiffContOnCl ℂ φ (ball (0 : ℂ) R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hR.ne']
    exact fun z hz => (hdiff z hz).differentiableAt.differentiableWithinAt
  have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc
    (C := C) (fun z hz => hb _ (hmem z (sphere_subset_closedBall hz)))
  rw [(hdiff 0 (mem_closedBall_self hR.le)).deriv] at hest
  simp only [zero_smul, add_zero] at hest
  calc ‖fderiv ℂ h y v‖ ≤ C / R := hest
    _ = C / ρ * ‖v‖ := by rw [hRdef]; field_simp

variable [CompleteSpace F]

/-- A uniform limit on an open set of ℂ-differentiable maps is ℂ-differentiable. -/
theorem differentiableOn_of_tendstoUniformlyOn {f : ℕ → E → F} {g : E → F} {s : Set E}
    (hs : IsOpen s) (hf : ∀ N, DifferentiableOn ℂ (f N) s)
    (hfg : TendstoUniformlyOn f g atTop s) : DifferentiableOn ℂ g s := by
  intro x hx
  obtain ⟨ρ2, hρ2, hball⟩ := Metric.isOpen_iff.mp hs x hx
  set ρ : ℝ := ρ2 / 3 with hρdef
  have hρ : 0 < ρ := by positivity
  have hsub : ∀ y ∈ ball x ρ, closedBall y ρ ⊆ s := by
    intro y hy z hz
    apply hball
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hz
    linarith [dist_triangle z y x]
  set f' : ℕ → E → (E →L[ℂ] F) := fun N y => fderiv ℂ (f N) y
  -- the derivatives are uniformly Cauchy on `ball x ρ`
  have hcauchy : UniformCauchySeqOn f' atTop (ball x ρ) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro δ hδ
    have hu := hfg.uniformCauchySeqOn
    rw [Metric.uniformCauchySeqOn_iff] at hu
    obtain ⟨N0, hN0⟩ := hu (δ * ρ / 2) (by positivity)
    refine ⟨N0, fun m hm n hn y hy => ?_⟩
    have hd : DifferentiableOn ℂ (f m - f n) s := (hf m).sub (hf n)
    have hest := norm_fderiv_le_of_closedBall hs hd hρ (by positivity : (0 : ℝ) ≤ δ * ρ / 2)
      (hsub y hy) (fun z hz => by
        have := hN0 m hm n hn z (hsub y hy hz)
        rw [dist_eq_norm] at this
        simpa using this.le)
    have hyS : s ∈ 𝓝 y := hs.mem_nhds (hsub y hy (mem_closedBall_self hρ.le))
    rw [fderiv_sub ((hf m).differentiableAt hyS) ((hf n).differentiableAt hyS)] at hest
    rw [dist_eq_norm]
    calc ‖f' m y - f' n y‖ ≤ δ * ρ / 2 / ρ := hest
      _ = δ / 2 := by field_simp
      _ < δ := by linarith
  have hlim : ∀ y ∈ ball x ρ, ∃ L, Tendsto (fun N => f' N y) atTop (𝓝 L) := fun y hy =>
    cauchySeq_tendsto_of_complete (hcauchy.cauchySeq hy)
  choose! g' hg' using hlim
  have hunif : TendstoUniformlyOn f' g' atTop (ball x ρ) :=
    hcauchy.tendstoUniformlyOn_of_tendsto hg'
  have hD : HasFDerivAt g (g' x) x := by
    refine hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hunif (fun N y hy => ?_)
      (fun y hy => hfg.tendsto_at (hsub y hy (mem_closedBall_self hρ.le)))
      (mem_ball_self hρ)
    exact ((hf N).differentiableAt
      (hs.mem_nhds (hsub y hy (mem_closedBall_self hρ.le)))).hasFDerivAt
  exact hD.differentiableAt.differentiableWithinAt

end ABC.S4.FlowHoloAux
