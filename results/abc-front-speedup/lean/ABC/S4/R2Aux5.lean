import ABC.S4.R2Aux4

/-! R2 helpers: `X(t)` is real on `[0, 2π]`, `tr X(2π) = jtr P₁ 0`, and the packaged
fundamental matrix. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)
open scoped ContDiff NNReal

noncomputable section

namespace ABC.S4.R2Aux

open ABC ABC.S4

section X

variable {H₁ : C2 → ℂ → ℂ} {ρ s s₀ r₀ : ℝ} {φ : ℂ → Cn 3 → Cn 3}

theorem Bm_real (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ) (hs : 0 < s) (t : ℝ) (i k : Fin 2) :
    (Bm H₁ t i k).im = 0 := by
  fin_cases i <;> fin_cases k <;> simp [Bm, Amat_real hH hρ hs]

theorem FlowData.X_real (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (hs : 0 < s) (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * π)) (i j : Fin 2) : (Xf φ t i j).im = 0 := by
  -- a bound on `B` over `[0, 2π + 1]`
  have hBc : ContinuousOn (fun u : ℝ => (fun i k => Bm H₁ u i k : Fin 2 → Fin 2 → ℂ))
      (Icc 0 (2 * π + 1)) := by
    have hA : ∀ i j, ContinuousOn (fun u : ℝ => Amat H₁ u i j) (Icc 0 (2 * π + 1)) := by
      intro i j
      refine ((Amat_holo hH hρ i j).continuousOn.comp Complex.continuous_ofReal.continuousOn ?_)
      intro u _; simp [strip, hs]
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ?_
    fin_cases i <;> fin_cases k <;> simp [Bm] <;> first | exact hA _ _ | exact (hA _ _).neg
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hBc
  have hC' : ∀ u ∈ Icc (0 : ℝ) (2 * π + 1), ∀ i k, ‖Bm H₁ u i k‖ ≤ C := fun u hu i k =>
    (norm_le_pi_norm (fun k => Bm H₁ u i k) k).trans
      ((norm_le_pi_norm (fun i k => Bm H₁ u i k) i).trans (hC u hu))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC' 0 ⟨le_rfl, by positivity⟩ 0 0)
  set v : ℝ → (Fin 2 → Fin 2 → ℂ) → (Fin 2 → Fin 2 → ℂ) :=
    fun u Y i j => ∑ k, Bm H₁ u i k * Y k j
  have hlip : ∀ u ∈ Icc (0 : ℝ) (2 * π + 1), LipschitzWith (Real.toNNReal (2 * C)) (v u) := by
    intro u hu
    refine LipschitzWith.of_dist_le_mul fun Y Y' => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    have hW : ∀ k, ‖Y k j - Y' k j‖ ≤ ‖Y - Y'‖ := fun k =>
      (norm_le_pi_norm (fun j => (Y - Y') k j) j).trans (norm_le_pi_norm (Y - Y') k)
    simp only [v, Pi.sub_apply, Fin.sum_univ_two]
    have e : ∀ a b c d e f : ℂ, a * c + b * d - (a * e + b * f) = a * (c - e) + b * (d - f) := by
      intros; ring
    rw [e]
    calc ‖Bm H₁ u i 0 * (Y 0 j - Y' 0 j) + Bm H₁ u i 1 * (Y 1 j - Y' 1 j)‖
        ≤ ‖Bm H₁ u i 0‖ * ‖Y 0 j - Y' 0 j‖ + ‖Bm H₁ u i 1‖ * ‖Y 1 j - Y' 1 j‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ C * ‖Y - Y'‖ + C * ‖Y - Y'‖ := by
          gcongr
          · exact hC' u hu i 0
          · exact hW 0
          · exact hC' u hu i 1
          · exact hW 1
      _ = 2 * C * ‖Y - Y'‖ := by ring
  have hXd : ∀ u ∈ Icc 0 (2 * π), HasDerivAt (fun u : ℝ => (fun i j => Xf φ u i j :
      Fin 2 → Fin 2 → ℂ)) (v u (fun i j => Xf φ u i j)) u := by
    intro u hu
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    have := hasDerivAt_ofReal_comp (fd.X_ode hH hρ h0 (real_mem_Dom fd.s₀pos hu) i j)
    simpa [v, Matrix.mul_apply] using this
  have heq := R2Aux.local_unique (v := v) (f := fun u : ℝ => (fun i j => Xf φ u i j :
      Fin 2 → Fin 2 → ℂ)) (g := fun u : ℝ => (fun i j => conj (Xf φ u i j)))
    (a := 0) (b := 2 * π)
    (fun u hu => ⟨1, one_pos, 1, one_pos, Real.toNNReal (2 * C), fun w hw =>
      (hlip w ⟨hu.1.trans hw.1, by linarith [hw.2, hu.2]⟩).lipschitzOnWith⟩)
    (fun u hu => (hXd u hu).hasDerivWithinAt)
    (fun u hu => by
      refine (hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_).hasDerivWithinAt
      have := ((hasDerivAt_pi.1 (hasDerivAt_pi.1 (hXd u hu) i)) j).star
      refine this.congr_deriv ?_
      simp only [v, star_sum, star_mul']
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      exact Complex.conj_eq_iff_im.2 (Bm_real hH hρ hs u i k))
    (by simp [fd.X_zero, Matrix.one_apply])
  have := congrFun (congrFun (heq ht) i) j
  exact Complex.conj_eq_iff_im.1 this.symm

/-- `jtr P₁ 0 = tr X(2π)`. -/
theorem FlowData.X_jtr (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (hs : 0 < s) (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) {P₁ : E 2 → E 2}
    (hP : IsPeriodMap H₁ P₁ ρ) :
    jtr P₁ 0 = (Xf φ (2 * π) 0 0 + Xf φ (2 * π) 1 1).re := by
  have h0' : ∀ t, hamVF (H₁ · t) 0 = 0 := by
    intro t; funext i; fin_cases i <;> simp [hamVF, (h0 t).2]
  have hPd : DifferentiableAt ℝ P₁ 0 :=
    (period_map_smooth hρ hs hH h0' hP hρ).1.differentiableAt (by simp)
  set liftL : E 2 →L[ℝ] Cn 3 := ContinuousLinearMap.pi
    ![Complex.ofRealCLM.comp (EuclideanSpace.proj 0),
      Complex.ofRealCLM.comp (EuclideanSpace.proj 1), 0]
  have hlift : ∀ x : E 2, liftL x = ![(x 0 : ℂ), (x 1 : ℂ), 0] := by
    intro x; funext i; fin_cases i <;> simp [liftL]
  set r := min ρ r₀
  have hr : 0 < r := lt_min hρ fd.r₀pos
  have hT : (2 * π : ℝ) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  -- on a ball, `P₁` is the time-`2π` flow
  have hflow : ∀ x : E 2, ‖x‖ < r → ∀ i : Fin 2,
      ((P₁ x i : ℝ) : ℂ) = φ (2 * π) (liftL x) (Fin.castSucc i) := by
    intro x hx i
    have hxρ : ‖x‖ < ρ := lt_of_lt_of_le hx (min_le_left _ _)
    obtain ⟨γ, hγ, hγ0, hγT⟩ := hP x hxρ
    have hxb : liftL x ∈ ball (0 : Cn 3) r₀ := by
      rw [mem_ball_zero_iff, hlift]
      refine (pi_norm_lt_iff fd.r₀pos).2 fun i => ?_
      have hle : ∀ k, ‖x k‖ ≤ ‖x‖ := fun k => PiLp.norm_apply_le x k
      have hxr : ‖x‖ < r₀ := lt_of_lt_of_le hx (min_le_right _ _)
      fin_cases i
      · simpa using lt_of_le_of_lt (hle 0) hxr
      · simpa using lt_of_le_of_lt (hle 1) hxr
      · simpa using fd.r₀pos
    set Γ : ℝ → Cn 3 := fun t => ![γ t 0, γ t 1, (t : ℂ)]
    have hΓ : ∀ t ∈ Icc 0 (2 * π), HasDerivWithinAt Γ (Fvf H₁ (Γ t)) (Icc 0 (2 * π)) t := by
      intro t ht
      have hw : wPart (Γ t) = γ t := by funext i; fin_cases i <;> rfl
      have h2 : Γ t 2 = t := rfl
      have hγt := hγ t ht
      have hFv : Fvf H₁ (Γ t) = ![hamVF (fun w => H₁ w t) (γ t) 0,
          hamVF (fun w => H₁ w t) (γ t) 1, 1] := by
        simp only [Fvf, hw, h2]
      rw [hFv]
      refine hasDerivWithinAt_pi.2 fun i => ?_
      fin_cases i
      · exact hasDerivWithinAt_pi.1 hγt 0
      · exact hasDerivWithinAt_pi.1 hγt 1
      · have : HasDerivWithinAt (fun t : ℝ => (t : ℂ)) 1 (Icc 0 (2 * π)) t := by
          simpa using ((hasDerivAt_id t).ofReal_comp).hasDerivWithinAt
        exact this
    have hΓ0 : Γ 0 = liftL x := by
      rw [hlift]; funext i; fin_cases i <;> simp [Γ, hγ0, ofR]
    have := fd.eq_of_solution hH hxb hΓ hΓ0 _ hT
    have hc := congrFun this (Fin.castSucc i)
    push_cast at hc
    rw [← hc]
    fin_cases i <;> simp [Γ, hγT, ofR]
  -- differentiate both sides
  have hT' : (2 * π : ℂ) ∈ Dom s₀ := by simpa using real_mem_Dom fd.s₀pos hT
  have hφd : HasFDerivAt (φ (2 * π)) (fderiv ℂ (φ (2 * π)) 0) 0 :=
    (fd.slice_diffAt hT' (mem_ball_self fd.r₀pos)).differentiableAt.hasFDerivAt
  have hcomp : ∀ i : Fin 2, ∀ y : E 2,
      ((fderiv ℝ P₁ 0 y i : ℝ) : ℂ) = fderiv ℂ (φ (2 * π)) 0 (liftL y) (Fin.castSucc i) := by
    intro i y
    have h1 : HasFDerivAt (fun x : E 2 => ((P₁ x i : ℝ) : ℂ))
        ((Complex.ofRealCLM.comp (EuclideanSpace.proj i)).comp (fderiv ℝ P₁ 0)) 0 :=
      (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).hasFDerivAt.comp 0 hPd.hasFDerivAt
    have hl0 : liftL 0 = 0 := map_zero _
    have h2 : HasFDerivAt (fun x : E 2 => φ (2 * π) (liftL x) (Fin.castSucc i))
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) (Fin.castSucc i)).comp
          (((fderiv ℂ (φ (2 * π)) 0).restrictScalars ℝ).comp liftL)) 0 := by
      have hφd' : HasFDerivAt (φ (2 * π)) ((fderiv ℂ (φ (2 * π)) 0).restrictScalars ℝ)
          (liftL 0) := by rw [hl0]; exact hφd.restrictScalars ℝ
      have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ)
        (Fin.castSucc i)).hasFDerivAt.comp 0 (hφd'.comp 0 liftL.hasFDerivAt)
      exact this
    have hev : (fun x : E 2 => ((P₁ x i : ℝ) : ℂ)) =ᶠ[𝓝 0]
        fun x => φ (2 * π) (liftL x) (Fin.castSucc i) := by
      filter_upwards [ball_mem_nhds (0 : E 2) hr] with x hx
      exact hflow x (by simpa using hx) i
    have := congrArg (fun L => L y) ((h1.congr_of_eventuallyEq hev.symm).unique h2)
    simpa using this
  have htr : jtr P₁ 0 = fderiv ℝ P₁ 0 (EuclideanSpace.single 0 1) 0 +
      fderiv ℝ P₁ 0 (EuclideanSpace.single 1 1) 1 := by
    unfold jtr
    rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
    simp [Matrix.trace, Fin.sum_univ_two, LinearMap.toMatrix_apply]
  have hs0 : liftL (EuclideanSpace.single 0 1) = Pi.single (Fin.castSucc 0) 1 := by
    rw [hlift]; funext i; fin_cases i <;> simp
  have hs1 : liftL (EuclideanSpace.single 1 1) = Pi.single (Fin.castSucc 1) 1 := by
    rw [hlift]; funext i; fin_cases i <;> simp
  rw [htr, Xf, Xf, ← hs0, ← hs1, ← hcomp, ← hcomp]
  simp

end X

end ABC.S4.R2Aux
