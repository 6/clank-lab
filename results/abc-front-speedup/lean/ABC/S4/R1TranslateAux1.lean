import ABC.S4.Defs

/-! R1 helpers: ODE uniqueness for a `C¹` field on an open set, a one-variable root by
contraction, and holomorphic dependence of a unique root on parameters. -/

open Set Metric Filter Topology

noncomputable section

namespace ABC.S4.R1TranslateAux

/-- Uniqueness for an autonomous `C¹` field on an open set (no global Lipschitz bound). -/
theorem ode_unique_C1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {F : E → E} {U : Set E} (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) {f g : ℝ → E} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (F (f t)) (Icc a b) t ∧ f t ∈ U)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (F (g t)) (Icc a b) t ∧ g t ∈ U)
    (h0 : f a = g a) : EqOn f g (Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.2 hba)
  have hfc : ContinuousOn f (Icc a b) := fun t ht => (hf t ht).1.continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hg t ht).1.continuousWithinAt
  have hKf : IsCompact (f '' Icc a b) := isCompact_Icc.image_of_continuousOn hfc
  have hKg : IsCompact (g '' Icc a b) := isCompact_Icc.image_of_continuousOn hgc
  have hfU : f '' Icc a b ⊆ U := by rintro _ ⟨t, ht, rfl⟩; exact (hf t ht).2
  have hgU : g '' Icc a b ⊆ U := by rintro _ ⟨t, ht, rfl⟩; exact (hg t ht).2
  obtain ⟨δ, hδ, hδU⟩ := hKf.exists_cthickening_subset_open hU hfU
  have hKδ : IsCompact (cthickening δ (f '' Icc a b)) := hKf.cthickening
  have hFc : ContinuousOn F U := hF.continuousOn
  have hDc : ContinuousOn (fderiv ℝ F) U := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨C, hC⟩ := hKδ.exists_bound_of_continuousOn (hDc.mono hδU)
  obtain ⟨B, hB⟩ := (hKf.union hKg).exists_bound_of_continuousOn
    (hFc.mono (union_subset hfU hgU))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (f a) (Or.inl (mem_image_of_mem f
    ⟨le_rfl, hab⟩)))
  set K : ℝ := max C (2 * B / δ) with hK
  have hK0 : 0 ≤ K := (div_nonneg (by linarith) hδ.le).trans (le_max_right _ _)
  have hlip : ∀ t ∈ Icc a b, ‖F (g t) - F (f t)‖ ≤ K * ‖g t - f t‖ := by
    intro t ht
    by_cases hd : ‖g t - f t‖ < δ
    · have hball : ball (f t) δ ⊆ cthickening δ (f '' Icc a b) :=
        ball_subset_closedBall.trans (closedBall_subset_cthickening (mem_image_of_mem f ht) δ)
      have hm := (convex_ball (f t) δ).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
        (fun x hx => (hF.differentiableOn one_ne_zero x (hδU (hball hx))).differentiableAt
          (hU.mem_nhds (hδU (hball hx))))
        (fun x hx => hC x (hball hx)) (mem_ball_self hδ)
        (by rwa [mem_ball, dist_eq_norm])
      exact hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · push Not at hd
      have h1 : ‖F (g t)‖ ≤ B := hB _ (Or.inr (mem_image_of_mem g ht))
      have h2 : ‖F (f t)‖ ≤ B := hB _ (Or.inl (mem_image_of_mem f ht))
      calc ‖F (g t) - F (f t)‖ ≤ ‖F (g t)‖ + ‖F (f t)‖ := norm_sub_le _ _
        _ ≤ 2 * B / δ * δ := by rw [div_mul_cancel₀ _ hδ.ne']; linarith
        _ ≤ 2 * B / δ * ‖g t - f t‖ :=
          mul_le_mul_of_nonneg_left hd (div_nonneg (by linarith) hδ.le)
        _ ≤ K * ‖g t - f t‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  have hv : ∀ t ∈ Ico a b, LipschitzOnWith K.toNNReal F {f t, g t} := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have hl := hlip t ⟨ht.1, ht.2.le⟩
    rw [Real.coe_toNNReal _ hK0]
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simp
    · rw [dist_eq_norm, dist_eq_norm, norm_sub_rev, norm_sub_rev (f t)]; exact hl
    · rw [dist_eq_norm, dist_eq_norm]; exact hl
    · simp
  have hIcc : ∀ t ∈ Ico a b, Icc a b ∈ 𝓝[≥] t := fun t ht =>
    mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun t => {f t, g t}) hv hfc
    (fun t ht => (hf t ⟨ht.1, ht.2.le⟩).1.mono_of_mem_nhdsWithin (hIcc t ht))
    (fun t _ => Or.inl rfl) hgc
    (fun t ht => (hg t ⟨ht.1, ht.2.le⟩).1.mono_of_mem_nhdsWithin (hIcc t ht))
    (fun t _ => Or.inr rfl) h0

/-- A root of a one-variable holomorphic map whose derivative stays near `a ≠ 0`, with an
injectivity estimate. -/
theorem root_of_deriv_near {g : ℂ → ℂ} {a : ℂ} {r : ℝ} (ha : a ≠ 0)
    (hg : ∀ u ∈ ball (0 : ℂ) r, DifferentiableAt ℂ g u)
    (hder : ∀ u ∈ ball (0 : ℂ) r, ‖deriv g u - a‖ ≤ ‖a‖ / 2)
    (h0 : ‖g 0‖ < ‖a‖ * r / 2) :
    (∃ u ∈ ball (0 : ℂ) r, g u = 0) ∧
      ∀ u ∈ ball (0 : ℂ) r, ∀ v ∈ ball (0 : ℂ) r, ‖a‖ / 2 * ‖u - v‖ ≤ ‖g u - g v‖ := by
  have ha' : 0 < ‖a‖ := norm_pos_iff.2 ha
  -- `h u = g u - a u` is `‖a‖/2`-Lipschitz on the ball
  have hh : ∀ u ∈ ball (0 : ℂ) r, ∀ v ∈ ball (0 : ℂ) r,
      ‖(g u - a * u) - (g v - a * v)‖ ≤ ‖a‖ / 2 * ‖u - v‖ := by
    intro u hu v hv
    have hd : ∀ x ∈ ball (0 : ℂ) r, HasDerivAt (fun x => g x - a * x) (deriv g x - a) x :=
      fun x hx => by
        exact ((hg x hx).hasDerivAt.sub ((hasDerivAt_id' x).const_mul a)).congr_deriv (by ring)
    exact (convex_ball (0 : ℂ) r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hd x hx).hasDerivWithinAt) (fun x hx => hder x hx) hv hu
  have hinj : ∀ u ∈ ball (0 : ℂ) r, ∀ v ∈ ball (0 : ℂ) r,
      ‖a‖ / 2 * ‖u - v‖ ≤ ‖g u - g v‖ := by
    intro u hu v hv
    have h1 := hh u hu v hv
    have h2 : ‖a * (u - v)‖ ≤ ‖g u - g v‖ + ‖(g u - a * u) - (g v - a * v)‖ := by
      have : a * (u - v) = (g u - g v) - ((g u - a * u) - (g v - a * v)) := by ring
      rw [this]; exact norm_sub_le _ _
    rw [norm_mul] at h2
    nlinarith
  refine ⟨?_, hinj⟩
  have hr : 0 < r := by
    have := norm_nonneg (g 0)
    nlinarith
  set r' : ℝ := 2 * ‖g 0‖ / ‖a‖ with hr'
  have hr'0 : 0 ≤ r' := by positivity
  have hr'r : r' < r := by
    rw [hr', div_lt_iff₀ ha']; linarith
  have hsub : closedBall (0 : ℂ) r' ⊆ ball 0 r := closedBall_subset_ball hr'r
  set T : ℂ → ℂ := fun u => u - g u / a with hT
  have hTd : ∀ u ∈ ball (0 : ℂ) r, ∀ v ∈ ball (0 : ℂ) r, ‖T u - T v‖ ≤ 1 / 2 * ‖u - v‖ := by
    intro u hu v hv
    have : T u - T v = -(((g u - a * u) - (g v - a * v)) / a) := by
      simp only [hT]; field_simp; ring
    rw [this, norm_neg, norm_div, div_le_iff₀ ha']
    have := hh u hu v hv
    linarith
  have hT0 : ‖T 0‖ = r' / 2 := by
    simp only [hT, hr', zero_sub, norm_neg, norm_div]; field_simp
  have hmaps : MapsTo T (closedBall 0 r') (closedBall 0 r') := by
    intro u hu
    rw [mem_closedBall, dist_zero_right] at hu ⊢
    have := hTd u (hsub (mem_closedBall_zero_iff.2 hu)) 0 (mem_ball_self hr)
    rw [sub_zero] at this
    calc ‖T u‖ ≤ ‖T u - T 0‖ + ‖T 0‖ := norm_le_norm_sub_add _ _
      _ ≤ r' := by linarith
  have hcon : ContractingWith (1 / 2 : NNReal) (hmaps.restrict T _ _) := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, dist_eq_norm]
    have := hTd x (hsub x.2) y (hsub y.2)
    simpa using this
  obtain ⟨u, hu, hfix, -⟩ := hcon.exists_fixedPoint' isClosed_closedBall.isComplete hmaps
    (mem_closedBall_self hr'0) (edist_ne_top _ _)
  refine ⟨u, hsub hu, ?_⟩
  have : u - g u / a = u := hfix
  have : g u / a = 0 := by linear_combination -this
  simpa [ha] using this

/-- A unique root of a holomorphic map depends holomorphically on the parameters. -/
theorem implicit_holo {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    {f : ℂ × P → ℂ} (hf : ContDiff ℂ 1 f) {D : Set P} (hD : IsOpen D) {r : ℝ} {U : P → ℂ}
    (hU : ∀ p ∈ D, U p ∈ ball (0 : ℂ) r ∧ f (U p, p) = 0)
    (huniq : ∀ p ∈ D, ∀ u ∈ ball (0 : ℂ) r, f (u, p) = 0 → u = U p)
    (hder : ∀ p ∈ D, fderiv ℂ f (U p, p) (1, 0) ≠ 0) :
    DifferentiableOn ℂ U D := by
  intro p₀ hp₀
  set x₀ : ℂ × P := (U p₀, p₀)
  set f' := fderiv ℂ f x₀
  set c := f' (1, 0)
  have hc : c ≠ 0 := hder p₀ hp₀
  have hsplit : ∀ (a : ℂ) (q : P), f' (a, q) = a * c + f' (0, q) := by
    intro a q
    have : ((a, q) : ℂ × P) = a • ((1 : ℂ), (0 : P)) + ((0 : ℂ), q) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  set L : ℂ × P →L[ℂ] ℂ × P := f'.prod (ContinuousLinearMap.snd ℂ ℂ P)
  set M : ℂ × P →L[ℂ] ℂ × P :=
    ((c⁻¹ • ((ContinuousLinearMap.fst ℂ ℂ P) -
      f'.comp ((ContinuousLinearMap.inr ℂ ℂ P).comp (ContinuousLinearMap.snd ℂ ℂ P))))).prod
      (ContinuousLinearMap.snd ℂ ℂ P)
  have h1 : Function.LeftInverse M L := by
    intro x
    simp only [L, M, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inr_apply]
    rw [hsplit x.1 x.2]
    ext
    · simp only [smul_eq_mul, add_sub_cancel_right]; field_simp
    · rfl
  have h2 : Function.RightInverse M L := by
    intro x
    simp only [L, M, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inr_apply]
    rw [hsplit]
    ext
    · simp only [smul_eq_mul]; field_simp; ring
    · rfl
  set Le := ContinuousLinearEquiv.equivOfInverse L M h1 h2
  set Θ : ℂ × P → ℂ × P := fun x => (f x, x.2)
  have hΘ : HasStrictFDerivAt Θ (Le : ℂ × P →L[ℂ] ℂ × P) x₀ :=
    (hf.contDiffAt.hasStrictFDerivAt one_ne_zero).prodMk hasStrictFDerivAt_snd
  have hΘx₀ : Θ x₀ = (0, p₀) := by simp [Θ, x₀, (hU p₀ hp₀).2]
  set LI := hΘ.localInverse Θ Le x₀
  have hLI : DifferentiableAt ℂ LI (Θ x₀) := hΘ.to_localInverse.differentiableAt
  have hlin : HasFDerivAt (fun p : P => ((0 : ℂ), p)) (ContinuousLinearMap.inr ℂ ℂ P) p₀ :=
    (ContinuousLinearMap.inr ℂ ℂ P).hasFDerivAt
  have hT : Tendsto (fun p : P => ((0 : ℂ), p)) (𝓝 p₀) (𝓝 (Θ x₀)) := by
    rw [hΘx₀]; exact (continuous_const.prodMk continuous_id).tendsto p₀
  have hUt : DifferentiableAt ℂ (fun p => (LI ((0 : ℂ), p)).1) p₀ := by
    have : DifferentiableAt ℂ LI ((0 : ℂ), p₀) := hΘx₀ ▸ hLI
    exact (this.comp p₀ hlin.differentiableAt).fst
  have hev : (fun p => (LI ((0 : ℂ), p)).1) =ᶠ[𝓝 p₀] U := by
    have hr := hT.eventually hΘ.eventually_right_inverse
    have hcont : Tendsto (fun p : P => LI ((0 : ℂ), p)) (𝓝 p₀) (𝓝 x₀) := by
      have := (hΘ.localInverse_continuousAt).tendsto.comp hT
      rwa [hΘ.localInverse_apply_image] at this
    have hball : ∀ᶠ p in 𝓝 p₀, (LI ((0 : ℂ), p)).1 ∈ ball (0 : ℂ) r :=
      (continuous_fst.tendsto x₀).comp hcont |>.eventually
        (isOpen_ball.mem_nhds (hU p₀ hp₀).1)
    filter_upwards [hr, hball, hD.mem_nhds hp₀] with p hp hpb hpD
    have h2 : (LI ((0 : ℂ), p)).2 = p := congrArg Prod.snd hp
    have h1 : f (LI ((0 : ℂ), p)) = 0 := congrArg Prod.fst hp
    apply huniq p hpD _ hpb
    have e : ((LI ((0 : ℂ), p)).1, p) = LI ((0 : ℂ), p) := Prod.ext rfl h2.symm
    rw [e]; exact h1
  exact (hUt.congr_of_eventuallyEq hev.symm).differentiableWithinAt

end ABC.S4.R1TranslateAux
