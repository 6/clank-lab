import ABC.Unit

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ABC

theorem zlatosKPP_smul {f : ℝ → ℝ} (hf : ZlatosKPP f) {a : ℝ} (ha : 0 < a) :
    ZlatosKPP (fun s => a * f s) := by
  obtain ⟨ε, hε0, hε1, hC, ⟨C, hHol⟩, h0, h1, hanti, hpos⟩ := hf
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      derivWithin (fun s => a * f s) (Set.Icc 0 1) s = a * derivWithin f (Set.Icc 0 1) s :=
    fun s hs => derivWithin_const_mul a ((hC.differentiableOn (by norm_num)) s hs)
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine ⟨ε, hε0, hε1, contDiffOn_const.mul hC, ⟨a * C, ?_⟩, by simp [h0], by simp [h1], ?_, ?_⟩
  · intro s hs t ht
    rw [hd s hs, hd t ht, ← mul_sub, abs_mul, abs_of_pos ha, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hHol s hs t ht) ha.le
  · intro s hs t ht hst
    exact mul_le_mul_of_nonneg_left (hanti hs ht hst) ha.le
  · intro s hs
    obtain ⟨hp, hle⟩ := hpos s hs
    refine ⟨mul_pos ha hp, ?_⟩
    rw [hd 0 h0mem, mul_left_comm]
    exact mul_le_mul_of_nonneg_left hle ha.le

/-- Product of uniform measures on the unit cube, the image of `volume` on `cell 3 1`. -/
private def μc : Measure (Fin 3 → ℝ) := Measure.pi (fun _ => volume.restrict (Set.Ico (0 : ℝ) 1))

local instance : IsProbabilityMeasure (volume.restrict (Set.Ico (0 : ℝ) 1)) :=
  ⟨by simp⟩

local instance : IsProbabilityMeasure μc := by unfold μc; infer_instance

private lemma cell_integral (g : E 3 → E 3) :
    ∫ x in cell 3 1, g x = ∫ y, g (WithLp.toLp 2 y) ∂μc := by
  have hmp := PiLp.volume_preserving_toLp (Fin 3)
  have h := hmp.setIntegral_preimage_emb (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
    g (cell 3 1)
  have hpre : (WithLp.toLp 2 : (Fin 3 → ℝ) → E 3) ⁻¹' cell 3 1 =
      Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1) := by
    ext y; simp [cell]
  rw [← h]
  change ∫ y in WithLp.toLp 2 ⁻¹' cell 3 1, g (WithLp.toLp 2 y) = _
  rw [hpre, volume_pi, Measure.restrict_pi_pi]
  rfl

/-- The linear form `x ↦ 2π x_m`. -/
private def ℓ (m : Fin 3) : E 3 →L[ℝ] ℝ := (2 * Real.pi) • EuclideanSpace.proj m

private lemma ℓ_apply (m : Fin 3) (x : E 3) : ℓ m x = 2 * Real.pi * x m := by
  simp [ℓ]

/-- Everything `ZlatosFlow` asks of a field except periodicity, with `D` its derivative;
closed under addition. -/
private structure Good (g : E 3 → E 3) (D : E 3 → E 3 →L[ℝ] E 3) : Prop where
  cd : ContDiff ℝ 1 g
  deriv : ∀ x, HasFDerivAt g (D x) x
  lip : ∃ K, ∀ x y, ‖D x - D y‖ ≤ K * ‖x - y‖
  div : ∀ x, ∑ i, D x (ev i) i = 0
  int : Integrable (fun y => g (WithLp.toLp 2 y)) μc
  int0 : ∫ y, g (WithLp.toLp 2 y) ∂μc = 0

private lemma Good.add {g₁ g₂ : E 3 → E 3} {D₁ D₂ : E 3 → E 3 →L[ℝ] E 3} (h₁ : Good g₁ D₁)
    (h₂ : Good g₂ D₂) : Good (fun x => g₁ x + g₂ x) (fun x => D₁ x + D₂ x) where
  cd := h₁.cd.add h₂.cd
  deriv x := (h₁.deriv x).add (h₂.deriv x)
  lip := by
    obtain ⟨K₁, hK₁⟩ := h₁.lip
    obtain ⟨K₂, hK₂⟩ := h₂.lip
    refine ⟨K₁ + K₂, fun x y => ?_⟩
    calc ‖D₁ x + D₂ x - (D₁ y + D₂ y)‖ = ‖(D₁ x - D₁ y) + (D₂ x - D₂ y)‖ := by abel_nf
      _ ≤ ‖D₁ x - D₁ y‖ + ‖D₂ x - D₂ y‖ := norm_add_le _ _
      _ ≤ K₁ * ‖x - y‖ + K₂ * ‖x - y‖ := add_le_add (hK₁ x y) (hK₂ x y)
      _ = (K₁ + K₂) * ‖x - y‖ := by ring
  div x := by simp [Finset.sum_add_distrib, h₁.div x, h₂.div x]
  int := h₁.int.add h₂.int
  int0 := by rw [integral_add h₁.int h₂.int, h₁.int0, h₂.int0, add_zero]

/-- One term `φ(2π x_m) e_j` of the field, with `m ≠ j`. -/
private lemma good_term {φ φ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt φ (φ' t) t)
    (hcd : ContDiff ℝ 1 φ) (hL : ∀ s t, |φ' s - φ' t| ≤ |s - t|) (hb : ∀ t, |φ t| ≤ 1)
    (hi : ∫ t in (0 : ℝ)..1, φ (2 * Real.pi * t) = 0) {m j : Fin 3} (hmj : m ≠ j) :
    Good (fun x => φ (ℓ m x) • ev j) (fun x => (φ' (ℓ m x) • ℓ m).smulRight (ev j)) where
  cd := (hcd.comp (ℓ m).contDiff).smul contDiff_const
  deriv x := ((hd (ℓ m x)).comp_hasFDerivAt x (ℓ m).hasFDerivAt).smul_const (ev j)
  lip := by
    refine ⟨‖ℓ m‖ * ‖(ev j : E 3)‖ * ‖ℓ m‖, fun x y => ?_⟩
    have hsub : (φ' (ℓ m x) • ℓ m).smulRight (ev j) - (φ' (ℓ m y) • ℓ m).smulRight (ev j) =
        ((φ' (ℓ m x) - φ' (ℓ m y)) • ℓ m).smulRight (ev j : E 3) := by
      ext z : 1; simp [sub_mul, sub_smul]
    rw [hsub, ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
    have h1 : |φ' (ℓ m x) - φ' (ℓ m y)| ≤ ‖ℓ m‖ * ‖x - y‖ := by
      refine (hL _ _).trans ?_
      rw [← map_sub, ← Real.norm_eq_abs]
      exact (ℓ m).le_opNorm _
    calc |φ' (ℓ m x) - φ' (ℓ m y)| * ‖ℓ m‖ * ‖(ev j : E 3)‖
        ≤ ‖ℓ m‖ * ‖x - y‖ * ‖ℓ m‖ * ‖(ev j : E 3)‖ := by gcongr
      _ = ‖ℓ m‖ * ‖(ev j : E 3)‖ * ‖ℓ m‖ * ‖x - y‖ := by ring
  div x := by
    fin_cases m <;> fin_cases j <;> simp_all [Fin.sum_univ_three, ℓ_apply]
  int := by
    refine Integrable.smul_const ?_ _
    refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun y => ?_)
    · exact (hcd.continuous.comp ((ℓ m).continuous.comp (PiLp.continuous_toLp 2 _)))
        |>.aestronglyMeasurable
    · simpa using hb _
  int0 := by
    rw [integral_smul_const]
    suffices h : ∫ y, φ (ℓ m (WithLp.toLp 2 y)) ∂μc = 0 by rw [h, zero_smul]
    have hc : Continuous fun t => φ (2 * Real.pi * t) := by
      have := hcd.continuous; fun_prop
    simp only [ℓ_apply]
    have hmap := integral_map (μ := μc) (measurable_pi_apply m).aemeasurable
      (f := fun t => φ (2 * Real.pi * t)) hc.aestronglyMeasurable
    rw [show μc.map (fun y => y m) = volume.restrict (Set.Ico (0 : ℝ) 1) from
      (measurePreserving_eval _ m).map_eq] at hmap
    rw [← hmap, integral_Ico_eq_integral_Ioo,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, hi]

private lemma good_sin {m j : Fin 3} (hmj : m ≠ j) :
    Good (fun x => Real.sin (ℓ m x) • ev j)
      (fun x => (Real.cos (ℓ m x) • ℓ m).smulRight (ev j)) :=
  good_term Real.hasDerivAt_sin Real.contDiff_sin Real.abs_cos_sub_cos_le
    Real.abs_sin_le_one
    (by rw [intervalIntegral.integral_comp_mul_left (fun t => Real.sin t) (by positivity)]; simp)
    hmj

private lemma good_cos {m j : Fin 3} (hmj : m ≠ j) :
    Good (fun x => Real.cos (ℓ m x) • ev j)
      (fun x => ((fun t => -Real.sin t) (ℓ m x) • ℓ m).smulRight (ev j)) :=
  good_term Real.hasDerivAt_cos Real.contDiff_cos
    (fun s t => by rw [neg_sub_neg, abs_sub_comm]; exact Real.abs_sin_sub_sin_le s t)
    Real.abs_cos_le_one
    (by rw [intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) (by positivity)]; simp)
    hmj

private lemma abcUnit_eq : abcUnit = fun x =>
    Real.sin (ℓ 2 x) • ev 0 + Real.cos (ℓ 1 x) • ev 0 + Real.sin (ℓ 0 x) • ev 1 +
      Real.cos (ℓ 2 x) • ev 1 + Real.sin (ℓ 1 x) • ev 2 + Real.cos (ℓ 0 x) • ev 2 := by
  funext x
  ext j
  fin_cases j <;> simp [abcUnit, abcField, ℓ_apply]

private lemma good_abcUnit : ∃ D, Good abcUnit D := by
  rw [abcUnit_eq]
  exact ⟨_, ((((((good_sin (by decide : (2 : Fin 3) ≠ 0)).add
    (good_cos (by decide : (1 : Fin 3) ≠ 0))).add
    (good_sin (by decide : (0 : Fin 3) ≠ 1))).add
    (good_cos (by decide : (2 : Fin 3) ≠ 1))).add
    (good_sin (by decide : (1 : Fin 3) ≠ 2))).add
    (good_cos (by decide : (0 : Fin 3) ≠ 2)))⟩

private lemma periodic_abcUnit : Periodic 1 abcUnit := by
  intro i x
  rw [abcUnit_eq]
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [ℓ_apply, mul_add, Real.sin_add_two_pi, Real.cos_add_two_pi]

theorem zlatosFlow_abcUnit : ZlatosFlow 1 abcUnit := by
  obtain ⟨D, hG⟩ := good_abcUnit
  obtain ⟨K, hK⟩ := hG.lip
  refine ⟨periodic_abcUnit, hG.cd, ⟨1, K, one_pos, le_rfl, fun x y => ?_⟩, fun x => ?_, ?_⟩
  · rw [(hG.deriv x).fderiv, (hG.deriv y).fderiv, Real.rpow_one]
    exact hK x y
  · unfold divergence
    rw [(hG.deriv x).fderiv]
    exact hG.div x
  · rw [cell_integral]
    exact hG.int0


end ABC
