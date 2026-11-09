import ABC.Defs

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ABC

/-! ### Helpers: the period cell, and Lipschitz periodic functions are in `H¹(Tⁿ)` -/

private lemma cell_eq (n : ℕ) :
    cell n 1 = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin n => Set.Ico (0:ℝ) 1) := by
  ext x; simp [cell]

private lemma measurableSet_cell (n : ℕ) : MeasurableSet (cell n 1) := by
  rw [cell_eq]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Ico).preimage (by fun_prop)

private lemma volume_cell (n : ℕ) : volume (cell n 1) = 1 := by
  rw [cell_eq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet]
  simp [Real.volume_pi_Ico]

private lemma isCompact_cube (n : ℕ) : IsCompact {x : E n | ∀ i, x i ∈ Set.Icc (0:ℝ) 1} := by
  have : {x : E n | ∀ i, x i ∈ Set.Icc (0:ℝ) 1} =
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) ⁻¹'
        (Set.univ.pi fun _ => Set.Icc 0 1) := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi]; rfl
  rw [this]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toHomeomorph.isCompact_preimage.2
    (isCompact_univ_pi fun _ => isCompact_Icc)

private lemma fderiv_ev_eq_gradient {n : ℕ} (w : E n → ℝ) (x : E n) (i : Fin n) :
    fderiv ℝ w x (ev i) = gradient w x i := by
  have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := ev i) (y := fderiv ℝ w x)
  rw [gradient, ← this, EuclideanSpace.inner_single_right]
  simp

private lemma measurable_gradient' {n : ℕ} (w : E n → ℝ) : Measurable (gradient w) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (E n)).symm.continuous.measurable.comp (measurable_fderiv ℝ w)

private lemma norm_gradient_le {n : ℕ} {w : E n → ℝ} {C : NNReal} (hw : LipschitzWith C w)
    (x : E n) :
    ‖gradient w x‖ ≤ C := by
  unfold gradient
  rw [LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hw


private lemma isWeakGradient_of_lipschitz {n : ℕ} {w : E n → ℝ} {C : NNReal}
    (hw : LipschitzWith C w) :
    IsWeakGradient w (gradient w) := by
  refine ⟨hw.continuous.locallyIntegrable, ?_, ?_⟩
  · rw [locallyIntegrable_iff]
    intro K hK
    refine Measure.integrableOn_of_bounded (M := C) hK.measure_lt_top.ne
      (measurable_gradient' w).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => norm_gradient_le hw x
  · intro φ hφ hφc i
    obtain ⟨D, hD⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp) 
    have h := hw.integral_lineDeriv_mul_eq (μ := volume) hD hφc (ev i)
    have h1 : ∫ x, lineDeriv ℝ w x (ev i) * φ x = ∫ x, gradient w x i * φ x := by
      refine integral_congr_ae ?_
      filter_upwards [hw.ae_differentiableAt (μ := volume)] with x hx
      rw [hx.lineDeriv_eq_fderiv, fderiv_ev_eq_gradient]
    have h2 : ∫ x, lineDeriv ℝ φ x (-ev i) * w x = - ∫ x, w x * fderiv ℝ φ x (ev i) := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have hd : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
      simp only [hd.lineDeriv_eq_fderiv, map_neg]
      ring
    rw [h1, h2] at h
    linarith


private lemma cell_subset_cube (n : ℕ) : cell n 1 ⊆ {x : E n | ∀ i, x i ∈ Set.Icc (0:ℝ) 1} :=
  fun _ hx i => Set.Ico_subset_Icc_self (hx i)

private lemma isH1Torus_of_lipschitz {n : ℕ} {w : E n → ℝ} {C : NNReal} (hw : LipschitzWith C w)
    (hper : Periodic 1 w) : IsH1Torus 1 w (gradient w) := by
  have hfin : volume (cell n 1) ≠ ⊤ := by simp [volume_cell]
  have : IsFiniteMeasure (volume.restrict (cell n 1)) := isFiniteMeasure_restrict.2 hfin
  refine ⟨hper, isWeakGradient_of_lipschitz hw, ?_, ?_⟩
  · obtain ⟨B, hB⟩ := (isCompact_cube n).exists_bound_of_continuousOn hw.continuous.continuousOn
    exact MemLp.of_bound (C := B) hw.continuous.aestronglyMeasurable
      ((ae_restrict_iff' (measurableSet_cell n)).2
        (Eventually.of_forall fun x hx => hB x (cell_subset_cube n hx)))
  · exact MemLp.of_bound (C := C) (measurable_gradient' w).aestronglyMeasurable
      (Eventually.of_forall fun x => norm_gradient_le hw x)


/-- Zlatoš's Remark 3 direction: a bounded Lipschitz first integral with
nonzero drift makes the variational formula positive. -/
theorem zlatosSup_pos {n : ℕ} (u : E n → E n) (f : ℝ → ℝ) (e : E n)
    (hf : ZlatosKPP f) (hu : ZlatosFlow 1 u) (w : E n → ℝ) (C : NNReal)
    (hw : LipschitzWith C w) (hper : Periodic 1 w) (hinv : ∀ᵐ x, ⟪u x, gradient w x⟫ = 0)
    (hβ : ∫ x in cell n 1, ⟪u x, e⟫ * w x ≠ 0) : 0 < zlatosSup u f e := by
  have hcell := measurableSet_cell n
  have hvol := volume_cell n
  have hfin : volume (cell n 1) ≠ ⊤ := by simp [hvol]
  have : IsFiniteMeasure (volume.restrict (cell n 1)) := isFiniteMeasure_restrict.2 hfin
  have hvolr : volume.real (cell n 1) = 1 := by simp [Measure.real, hvol]
  -- `f′(0) > 0`
  have hf0 : 0 < fderiv0 f := by
    obtain ⟨ε, -, -, -, -, -, -, -, h⟩ := hf
    obtain ⟨h1, h2⟩ := h (1 / 2) ⟨by norm_num, by norm_num⟩
    unfold fderiv0; linarith
  obtain ⟨-, hucd, -, -, hint⟩ := hu
  have hucont : Continuous u := hucd.continuous
  have hwc : Continuous w := hw.continuous
  have hcube := isCompact_cube n
  have hsub := cell_subset_cube n
  have hintc : ∀ g : E n → ℝ, Continuous g → Integrable g (volume.restrict (cell n 1)) :=
    fun g hg => (hg.continuousOn.integrableOn_compact hcube).mono_set hsub
  have hue0 : ∫ x in cell n 1, ⟪u x, e⟫ = 0 := by
    have hui : Integrable u (volume.restrict (cell n 1)) :=
      (hucont.continuousOn.integrableOn_compact hcube).mono_set hsub
    have h := integral_inner (𝕜 := ℝ) hui e
    rw [hint, inner_zero_right] at h
    rw [← h]
    congr 1; ext x; exact real_inner_comm _ _
  obtain ⟨M, hM⟩ := hcube.exists_bound_of_continuousOn (f := fun x => ⟪u x, e⟫)
    (by fun_prop)
  obtain ⟨B, hB⟩ := hcube.exists_bound_of_continuousOn hw.continuous.continuousOn
  set β := ∫ x in cell n 1, ⟪u x, e⟫ * w x with hβdef
  set γ := ∫ x in cell n 1, ⟪u x, e⟫ * w x ^ 2 with hγdef
  -- a small parameter `s > 0`
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s * |γ| < 2 ∧ |s * β| * |B| < 1 / 2 ∧
      (s * β) ^ 2 * (C : ℝ) ^ 2 < fderiv0 f / 4 := by
    refine (eventually_mem_nhdsWithin).and (nhdsWithin_le_nhds ?_)
    refine ((ContinuousAt.eventually_lt (f := fun s : ℝ => s * |γ|) (by fun_prop)
      continuousAt_const (by simp)).and ((ContinuousAt.eventually_lt
        (f := fun s : ℝ => |s * β| * |B|) (by fun_prop) continuousAt_const (by simp)).and
      (ContinuousAt.eventually_lt (f := fun s : ℝ => (s * β) ^ 2 * (C : ℝ) ^ 2) (by fun_prop)
        continuousAt_const (by simp; linarith)))).mono fun s hs => hs
  obtain ⟨s, hs0, hsγ, hsB, hsC⟩ := hev.exists
  set t := s * β with ht
  set wt : E n → ℝ := fun x => 1 + t * w x with hwt
  have hwtc : Continuous wt := continuous_const.add (continuous_const.mul hwc)
  have hwtL : LipschitzWith (‖t‖₊ * C) wt := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [hwt, Real.dist_eq, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
    rw [show 1 + t * w x - (1 + t * w y) = t * (w x - w y) by ring, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.dist_eq] using hw.dist_le_mul x y)
      (abs_nonneg t)
  have hwtP : Periodic 1 wt := fun i x => by simp only [hwt, hper i x]
  have hgrad : ∀ᵐ x, gradient wt x = t • gradient w x := by
    filter_upwards [hw.ae_differentiableAt (μ := volume)] with x hx
    have h : HasFDerivAt wt (t • fderiv ℝ w x) x :=
      (hx.hasFDerivAt.const_mul t).const_add 1
    rw [gradient, h.fderiv, gradient, map_smul]
  have hFI : FirstIntegral u wt (gradient wt) := by
    refine ⟨isH1Torus_of_lipschitz hwtL hwtP, ?_⟩
    filter_upwards [hinv, hgrad] with x h1 h2
    rw [h2, inner_smul_right, h1, mul_zero]
  -- the denominator is at least `1 / 4`
  have hwt_half : ∀ x ∈ cell n 1, 1 / 2 ≤ wt x := by
    intro x hx
    have h1 : |w x| ≤ |B| := (hB x (hsub hx)).trans (le_abs_self B)
    have h2 : |t * w x| ≤ 1 / 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left h1 (abs_nonneg t)).trans hsB.le
    simp only [hwt]
    linarith [neg_abs_le (t * w x)]
  have hD : 1 / 4 ≤ ∫ x in cell n 1, wt x ^ 2 := by
    have h : ∫ x in cell n 1, (1 / 4 : ℝ) ≤ ∫ x in cell n 1, wt x ^ 2 :=
      setIntegral_mono_on (integrable_const (μ := volume.restrict (cell n 1)) _)
        (hintc _ (by fun_prop)) hcell fun x hx => by nlinarith [hwt_half x hx]
    simpa [hvolr] using h
  -- the constraint
  have hcon : ∫ x in cell n 1, ‖gradient wt x‖ ^ 2 ≤ fderiv0 f * ∫ x in cell n 1, wt x ^ 2 := by
    have h : ∫ x in cell n 1, ‖gradient wt x‖ ^ 2 ≤ ∫ x in cell n 1, (|t| * C) ^ 2 :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
        (integrable_const (μ := volume.restrict (cell n 1)) _) (Eventually.of_forall fun x =>
          pow_le_pow_left₀ (norm_nonneg _) ((norm_gradient_le hwtL x).trans_eq (by simp)) 2)
    have h' : (|t| * C) ^ 2 = t ^ 2 * (C : ℝ) ^ 2 := by rw [mul_pow, sq_abs]
    simp only [h', integral_const, smul_eq_mul] at h
    simp only [measureReal_restrict_apply_univ, hvolr, one_mul] at h
    nlinarith
  -- the numerator
  have hN : ∫ x in cell n 1, ⟪u x, e⟫ * wt x ^ 2 = s * β ^ 2 * (2 + s * γ) := by
    have h : (fun x => ⟪u x, e⟫ * wt x ^ 2) = fun x =>
        ⟪u x, e⟫ + ((2 * t) * (⟪u x, e⟫ * w x) + t ^ 2 * (⟪u x, e⟫ * w x ^ 2)) := by
      ext x; simp only [hwt]; ring
    have i0 := hintc (fun x => ⟪u x, e⟫) (by fun_prop)
    have i1 := hintc (fun x => ⟪u x, e⟫ * w x) (by fun_prop)
    have i2 := hintc (fun x => ⟪u x, e⟫ * w x ^ 2) (by fun_prop)
    rw [h, integral_add i0 (by exact (i1.const_mul _).add (i2.const_mul _)),
      integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
      hue0, ht]
    ring
  have hpos : 0 < (∫ x in cell n 1, ⟪u x, e⟫ * wt x ^ 2) / ∫ x in cell n 1, wt x ^ 2 := by
    rw [hN]
    have : 0 < 2 + s * γ := by
      have := neg_abs_le γ; nlinarith
    exact div_pos (by positivity) (by linarith)
  -- the set is bounded above
  have hbdd : BddAbove {r | ∃ w g, FirstIntegral u w g ∧
      ∫ x in cell n 1, ‖g x‖ ^ 2 ≤ fderiv0 f * ∫ x in cell n 1, w x ^ 2 ∧
      r = (∫ x in cell n 1, ⟪u x, e⟫ * w x ^ 2) / ∫ x in cell n 1, w x ^ 2} := by
    refine ⟨|M|, ?_⟩
    rintro r ⟨w', g', hFI', -, rfl⟩
    have hw2 : Integrable (fun x => w' x ^ 2) (volume.restrict (cell n 1)) :=
      hFI'.1.2.2.1.integrable_sq
    have hD' : 0 ≤ ∫ x in cell n 1, w' x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hN' : ∫ x in cell n 1, ⟪u x, e⟫ * w' x ^ 2 ≤ |M| * ∫ x in cell n 1, w' x ^ 2 := by
      rw [← integral_const_mul]
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (hw2.const_mul _) ?_
      refine (ae_restrict_iff' hcell).2 (Eventually.of_forall fun x hx => ?_)
      rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right ((hM x (hsub hx)).trans (le_abs_self M)) (sq_nonneg _)
    rcases hD'.eq_or_lt with h | h
    · rw [← h, div_zero]; exact abs_nonneg M
    · rwa [div_le_iff₀ h]
  exact hpos.trans_le (le_csSup hbdd ⟨wt, gradient wt, hFI, hcon, rfl⟩)

end ABC
