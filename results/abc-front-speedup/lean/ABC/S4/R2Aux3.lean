import ABC.S4.R2Aux2

/-! R2 helpers: the flow of `Fvf` in complex time (from `flow_complex_time`), the variational
equation, and the fundamental matrix `Xf` of the linearisation at `w = 0`. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)
open scoped ContDiff

noncomputable section

namespace ABC.S4.R2Aux

open ABC ABC.S4

/-- The complex-time box around `[0, 2π]`. -/
def Dom (s₀ : ℝ) : Set ℂ := {t | t.re ∈ Ioo (-s₀) (2 * π + s₀) ∧ |t.im| < s₀}

theorem isOpen_Dom (s₀ : ℝ) : IsOpen (Dom s₀) :=
  (isOpen_Ioo.preimage Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

theorem convex_Dom (s₀ : ℝ) : Convex ℝ (Dom s₀) := by
  have : Dom s₀ = Complex.re ⁻¹' Ioo (-s₀) (2 * π + s₀) ∩ Complex.im ⁻¹' Ioo (-s₀) s₀ := by
    ext t; simp [Dom, abs_lt]
  rw [this]
  exact ((convex_Ioo _ _).linear_preimage Complex.reLm).inter
    ((convex_Ioo _ _).linear_preimage Complex.imLm)

theorem real_mem_Dom {s₀ : ℝ} (hs₀ : 0 < s₀) {t : ℝ} (ht : t ∈ Icc 0 (2 * π)) :
    (t : ℂ) ∈ Dom s₀ :=
  ⟨⟨by simp; linarith [ht.1], by simp; linarith [ht.2]⟩, by simp [hs₀]⟩

theorem Dom_mono {s₀ s₁ : ℝ} (h : s₁ ≤ s₀) : Dom s₁ ⊆ Dom s₀ := fun t ht =>
  ⟨⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩, by linarith [ht.2]⟩

theorem Dom_strip {s₀ s : ℝ} (h : s₀ ≤ s) : Dom s₀ ⊆ strip s := fun t ht => by
  simp only [strip, mem_setOf_eq]; linarith [ht.2]

structure FlowData (H₁ : C2 → ℂ → ℂ) (ρ s s₀ r₀ : ℝ) (φ : ℂ → Cn 3 → Cn 3) : Prop where
  s₀pos : 0 < s₀
  s₀le : s₀ ≤ s
  s₀le1 : s₀ ≤ 1
  r₀pos : 0 < r₀
  holo : DifferentiableOn ℂ (fun q : ℂ × Cn 3 => φ q.1 q.2) (Dom s₀ ×ˢ ball 0 r₀)
  init : ∀ x ∈ ball (0 : Cn 3) r₀, φ 0 x = x
  ode : ∀ x ∈ ball (0 : Cn 3) r₀, ∀ t ∈ Dom s₀, HasDerivAt (φ · x) (Fvf H₁ (φ t x)) t
  mem : ∀ x ∈ ball (0 : Cn 3) r₀, ∀ t ∈ Dom s₀, φ t x ∈ Uset ρ s

section Flow

variable {H₁ : C2 → ℂ → ℂ} {ρ s : ℝ}

theorem axisPt_zero : axisPt 0 = 0 := by funext i; fin_cases i <;> rfl

theorem hasDerivAt_axis (t : ℝ) :
    HasDerivAt (fun t : ℝ => axisPt (t : ℂ)) ![0, 0, 1] t := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · simpa [axisPt] using (hasDerivAt_id t).ofReal_comp

theorem flow_exists (hρ : 0 < ρ) (hs : 0 < s) (hH : IsTPHam H₁ ρ s)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) :
    ∃ s₀ r₀ φ, FlowData H₁ ρ s s₀ r₀ φ := by
  have hT : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨s₀, hs₀, r₀, hr₀, φ, hΦ, hφ⟩ := flow_complex_time (isOpen_Uset ρ s) (Fvf_holo hH)
    (γ := fun t : ℝ => axisPt (t : ℂ)) hT fun t _ => by
      refine ⟨?_, axis_mem hρ (by simp [strip, hs])⟩
      rw [Fvf_axis h0]; exact (hasDerivAt_axis t).hasDerivWithinAt
  simp only [Complex.ofReal_zero, axisPt_zero] at hΦ hφ
  set s₁ := min s₀ (min s 1)
  have hs₁ : 0 < s₁ := lt_min hs₀ (lt_min hs one_pos)
  have hsub : Dom s₁ ⊆ Dom s₀ := Dom_mono (min_le_left _ _)
  refine ⟨s₁, r₀, φ, hs₁, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _), hr₀,
    hΦ.mono (prod_mono hsub subset_rfl), fun x hx => (hφ x hx).1,
    fun x hx t ht => ((hφ x hx).2 t (hsub ht).1 (hsub ht).2).1,
    fun x hx t ht => ((hφ x hx).2 t (hsub ht).1 (hsub ht).2).2⟩

variable {s₀ r₀ : ℝ} {φ : ℂ → Cn 3 → Cn 3}

theorem FlowData.Ω_open (fd : FlowData H₁ ρ s s₀ r₀ φ) : IsOpen (Dom s₀ ×ˢ ball (0 : Cn 3) r₀) :=
  (isOpen_Dom s₀).prod isOpen_ball

theorem FlowData.zero_mem (fd : FlowData H₁ ρ s s₀ r₀ φ) : (0 : ℂ) ∈ Dom s₀ :=
  ⟨⟨by simp; linarith [fd.s₀pos], by simp; linarith [fd.s₀pos, Real.pi_pos]⟩, by simp [fd.s₀pos]⟩

theorem FlowData.slice_diffAt (fd : FlowData H₁ ρ s s₀ r₀ φ) {t : ℂ} (ht : t ∈ Dom s₀)
    {x : Cn 3} (hx : x ∈ ball (0 : Cn 3) r₀) :
    HasFDerivAt (φ t) ((fderiv ℂ (fun q : ℂ × Cn 3 => φ q.1 q.2) (t, x)).comp
      (ContinuousLinearMap.inr ℂ ℂ (Cn 3))) x :=
  (fd.holo.differentiableAt (fd.Ω_open.mem_nhds (mk_mem_prod ht hx))).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_right t x)

/-- The `τ`-component is `τ₀ + t`. -/
theorem FlowData.tau (fd : FlowData H₁ ρ s s₀ r₀ φ) {x : Cn 3} (hx : x ∈ ball (0 : Cn 3) r₀)
    {t : ℂ} (ht : t ∈ Dom s₀) : φ t x 2 = x 2 + t := by
  have hd : ∀ t ∈ Dom s₀, HasDerivAt (fun t => φ t x 2) 1 t := by
    intro t ht
    have := hasDerivAt_pi.1 (fd.ode x hx t ht) 2
    simpa [Fvf] using this
  have := (isOpen_Dom s₀).eqOn_of_deriv_eq (convex_Dom s₀).isPreconnected
    (f := fun t => φ t x 2) (g := fun t => x 2 + t)
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t _ => (differentiableAt_id.const_add _).differentiableWithinAt)
    (fun t ht => by simp [(hd t ht).deriv]) fd.zero_mem (by simp [fd.init x hx]) ht
  simpa using this

/-- A solution of `Fvf` on `[0, 2π]` starting in the ball is the flow. -/
theorem FlowData.eq_of_solution (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s)
    {x : Cn 3} (hx : x ∈ ball (0 : Cn 3) r₀) {g : ℝ → Cn 3}
    (hg : ∀ t ∈ Icc 0 (2 * π), HasDerivWithinAt g (Fvf H₁ (g t)) (Icc 0 (2 * π)) t)
    (hg0 : g 0 = x) : ∀ t ∈ Icc 0 (2 * π), g t = φ t x := by
  have hψ : ∀ t ∈ Icc 0 (2 * π),
      HasDerivWithinAt (fun t : ℝ => φ t x) (Fvf H₁ (φ t x)) (Icc 0 (2 * π)) t := fun t ht =>
    (hasDerivAt_ofReal_comp (fd.ode x hx _ (real_mem_Dom fd.s₀pos ht))).hasDerivWithinAt
  have := R2Aux.local_unique (v := fun _ => Fvf H₁) (f := fun t : ℝ => φ t x) (g := g)
    (fun t ht => by
      have hmem := fd.mem x hx _ (real_mem_Dom fd.s₀pos (Ico_subset_Icc_self ht))
      have hc : ContDiffAt ℂ 1 (Fvf H₁) (φ t x) :=
        (HoloDeriv.contDiffAt (isOpen_Uset ρ s) (Fvf_holo hH) hmem).of_le (by simp)
      obtain ⟨K, n, hn, hK⟩ := hc.exists_lipschitzOnWith
      obtain ⟨ε, hε, hεn⟩ := Metric.mem_nhds_iff.1 hn
      exact ⟨1, one_pos, ε, hε, K, fun _ _ => hK.mono hεn⟩)
    hψ hg (by simp [fd.init x hx, hg0])
  exact fun t ht => (this ht).symm

/-- Along the zero solution the flow is the axis. -/
theorem FlowData.axis (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) {t : ℂ} (ht : t ∈ Dom s₀) :
    φ t 0 = axisPt t := by
  have h0b : (0 : Cn 3) ∈ ball (0 : Cn 3) r₀ := mem_ball_self fd.r₀pos
  have hreal : ∀ y ∈ Icc 0 (2 * π), φ (y : ℂ) 0 = axisPt y := fun y hy =>
    (fd.eq_of_solution hH h0b (g := fun t : ℝ => axisPt (t : ℂ))
      (fun t _ => by rw [Fvf_axis h0]; exact (hasDerivAt_axis t).hasDerivWithinAt)
      (by simp [axisPt_zero]) y hy).symm
  have hf : AnalyticOnNhd ℂ (fun t => φ t 0) (Dom s₀) := by
    refine DifferentiableOn.analyticOnNhd ?_ (isOpen_Dom s₀)
    intro t ht
    exact ((fd.ode 0 h0b t ht).differentiableAt).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ axisPt (Dom s₀) := by
    refine DifferentiableOn.analyticOnNhd ?_ (isOpen_Dom s₀)
    exact (differentiable_pi.2 fun i => by fin_cases i <;> simp [axisPt]).differentiableOn
  have hπ : ((π : ℝ) : ℂ) ∈ Dom s₀ := real_mem_Dom fd.s₀pos ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩
  refine hf.eqOn_of_preconnected_of_frequently_eq hg (convex_Dom s₀).isPreconnected hπ ?_ ht
  have htend : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[≠] π) (𝓝[≠] (π : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
  refine htend.frequently (Filter.Eventually.frequently ?_)
  have : Icc 0 (2 * π) ∈ 𝓝 π := Icc_mem_nhds Real.pi_pos (by linarith [Real.pi_pos])
  filter_upwards [nhdsWithin_le_nhds this] with y hy
  exact hreal y hy

/-- The variational equation. -/
theorem FlowData.var (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) {t : ℂ}
    (ht : t ∈ Dom s₀) :
    HasDerivAt (fun t => fderiv ℂ (φ t) 0)
      ((fderiv ℂ (Fvf H₁) (φ t 0)).comp (fderiv ℂ (φ t) 0)) t := by
  set Φ : ℂ × Cn 3 → Cn 3 := fun q => φ q.1 q.2 with hΦdef
  have h0b : (0 : Cn 3) ∈ ball (0 : Cn 3) r₀ := mem_ball_self fd.r₀pos
  have hO := fd.Ω_open
  have hmem : (t, (0 : Cn 3)) ∈ Dom s₀ ×ˢ ball (0 : Cn 3) r₀ := mk_mem_prod ht h0b
  have hc : ContDiffAt ℂ ∞ Φ (t, 0) := HoloDeriv.contDiffAt hO fd.holo hmem
  have hsymm : IsSymmSndFDerivAt ℂ Φ (t, 0) := hc.isSymmSndFDerivAt (by simp)
  have hdΦ : DifferentiableAt ℂ (fderiv ℂ Φ) (t, 0) :=
    HoloDeriv.differentiableAt_fderiv hO fd.holo hmem
  -- (a) the slice derivative
  have ha : ∀ t' ∈ Dom s₀, fderiv ℂ (φ t') 0 = (fderiv ℂ Φ (t', 0)).comp
      (ContinuousLinearMap.inr ℂ ℂ (Cn 3)) := fun t' ht' => (fd.slice_diffAt ht' h0b).fderiv
  -- (b) the time derivative
  have hb : ∀ x ∈ ball (0 : Cn 3) r₀, fderiv ℂ Φ (t, x) (1, 0) = Fvf H₁ (φ t x) := by
    intro x hx
    have hΦd : HasFDerivAt Φ (fderiv ℂ Φ (t, x)) (t, x) :=
      (fd.holo.differentiableAt (hO.mem_nhds (mk_mem_prod ht hx))).hasFDerivAt
    have h1 : HasDerivAt (fun t' => Φ (t', x)) (fderiv ℂ Φ (t, x) (1, 0)) t :=
      hΦd.comp_hasDerivAt (f := fun t' : ℂ => (t', x)) t
        ((hasDerivAt_id' t).prodMk (hasDerivAt_const t x))
    exact h1.unique (fd.ode x hx t ht)
  -- (c), (d)
  have hc' : HasDerivAt (fun t' => fderiv ℂ Φ (t', 0)) (fderiv ℂ (fderiv ℂ Φ) (t, 0) (1, 0)) t :=
    hdΦ.hasFDerivAt.comp_hasDerivAt (f := fun t' : ℂ => (t', (0 : Cn 3))) t
      ((hasDerivAt_id' t).prodMk (hasDerivAt_const t (0 : Cn 3)))
  have hd' := hc'.clm_comp (hasDerivAt_const t (ContinuousLinearMap.inr ℂ ℂ (Cn 3)))
  simp only [ContinuousLinearMap.comp_zero, add_zero] at hd'
  have he : (fun t' => fderiv ℂ (φ t') 0) =ᶠ[𝓝 t]
      fun t' => (fderiv ℂ Φ (t', 0)).comp (ContinuousLinearMap.inr ℂ ℂ (Cn 3)) := by
    filter_upwards [(isOpen_Dom s₀).mem_nhds ht] with t' ht' using ha t' ht'
  refine (hd'.congr_of_eventuallyEq he).congr_deriv ?_
  -- (f) identify the derivative
  ext1 y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  rw [hsymm]
  have hx1 : HasFDerivAt (fun x => fderiv ℂ Φ (t, x)) ((fderiv ℂ (fderiv ℂ Φ) (t, 0)).comp
      (ContinuousLinearMap.inr ℂ ℂ (Cn 3))) 0 :=
    hdΦ.hasFDerivAt.comp 0 (hasFDerivAt_prodMk_right t 0)
  have hx2 := hx1.clm_apply (hasFDerivAt_const ((1 : ℂ), (0 : Cn 3)) 0)
  have hev : (fun x => fderiv ℂ Φ (t, x) (1, 0)) =ᶠ[𝓝 0] fun x => Fvf H₁ (φ t x) := by
    filter_upwards [isOpen_ball.mem_nhds h0b] with x hx using hb x hx
  have hFd : DifferentiableAt ℂ (Fvf H₁) (φ t 0) :=
    (Fvf_holo hH).differentiableAt ((isOpen_Uset ρ s).mem_nhds (fd.mem 0 h0b t ht))
  have hx3 : HasFDerivAt (fun x => Fvf H₁ (φ t x))
      ((fderiv ℂ (Fvf H₁) (φ t 0)).comp (fderiv ℂ (φ t) 0)) 0 :=
    hFd.hasFDerivAt.comp 0 (fd.slice_diffAt ht h0b).differentiableAt.hasFDerivAt
  have := congrArg (fun L => L y) ((hx2.congr_of_eventuallyEq hev.symm).unique hx3)
  simpa using this

end Flow

end ABC.S4.R2Aux
