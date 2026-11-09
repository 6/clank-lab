import ABC.S4.R3AuxP

/-! R3 auxiliaries: the periodic homological equation `f' + iκf = g` (design S3). -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real MeasureTheory

noncomputable section

namespace ABC.S4.R3Aux

open ABC.S4

/-- periodic solution of `f' + iκ f = g`, `κ ∉ ℤ` -/
def solK (κ : ℝ) (g : ℂ → ℂ) (t : ℂ) : ℂ :=
  (Complex.exp (2 * π * Complex.I * κ) - 1)⁻¹ *
    ∫ σ in (0 : ℝ)..2 * π, Complex.exp (Complex.I * κ * σ) * g (t + σ)

/-- the mean of `g` over a real period -/
def avg (g : ℂ → ℂ) : ℂ := ((2 * π : ℝ) : ℂ)⁻¹ * ∫ σ in (0 : ℝ)..2 * π, g σ

/-- periodic solution of `f' = g - avg g` -/
def sol0 (g : ℂ → ℂ) (t : ℂ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ σ in (0 : ℝ)..2 * π, (σ : ℂ) * g (t + σ)

lemma isOpen_strip' (s : ℝ) : IsOpen (strip s) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

lemma add_ofReal_mem_strip {s : ℝ} {t : ℂ} (ht : t ∈ strip s) (σ : ℝ) :
    t + (σ : ℂ) ∈ strip s := by
  simpa [strip] using ht

lemma isPreconnected_strip (s : ℝ) : IsPreconnected (strip s) := by
  have : strip s = Complex.imLm ⁻¹' Ioo (-s) s := by
    ext z; simp [strip, abs_lt]
  rw [this]
  exact ((convex_Ioo _ _).linear_preimage Complex.imLm).isPreconnected

lemma cont_shift {g : ℂ → ℂ} {s : ℝ} (hg : ContinuousOn g (strip s)) {t : ℂ}
    (ht : t ∈ strip s) : Continuous fun σ : ℝ => g (t + σ) :=
  hg.comp_continuous (continuous_const.add Complex.continuous_ofReal)
    (fun σ => add_ofReal_mem_strip ht σ)

lemma ftc_shift {W W' : ℂ → ℂ} (hW : ∀ z, HasDerivAt W (W' z) z) (hW' : Continuous W')
    {g : ℂ → ℂ} {s : ℝ} (hg : HolPer g s) {t : ℂ} (ht : t ∈ strip s) :
    ∫ σ in (0:ℝ)..2 * π, W σ * deriv g (t + σ) =
      (W ((2 * π : ℝ) : ℂ) - W 0) * g t - ∫ σ in (0:ℝ)..2 * π, W' σ * g (t + σ) := by
  have hd : ∀ σ : ℝ, HasDerivAt (fun σ : ℝ => W σ * g (t + σ))
      (W' σ * g (t + σ) + W σ * deriv g (t + σ)) σ := by
    intro σ
    have hg' : HasDerivAt g (deriv g (t + σ)) (t + σ) :=
      (hg.holo.differentiableAt ((isOpen_strip' s).mem_nhds
        (add_ofReal_mem_strip ht σ))).hasDerivAt
    have h1 : HasDerivAt (fun z => g (t + z)) (deriv g (t + σ)) σ := hg'.comp_const_add t σ
    exact ((hW σ).mul h1).comp_ofReal
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun z => (hW z).continuousAt
  have hc1 : Continuous fun σ : ℝ => W' σ * g (t + σ) :=
    (hW'.comp Complex.continuous_ofReal).mul (cont_shift hg.holo.continuousOn ht)
  have hc2 : Continuous fun σ : ℝ => W σ * deriv g (t + σ) :=
    (hWc.comp Complex.continuous_ofReal).mul
      (cont_shift (hg.holo.deriv (isOpen_strip' s)).continuousOn ht)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * π) (fun σ _ => hd σ)
    ((hc1.add hc2).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _)] at this
  have hp : g (t + ((2 * π : ℝ) : ℂ)) = g t := by push_cast; exact hg.per t
  simp only [hp, Complex.ofReal_zero, add_zero] at this
  linear_combination this

lemma hasDerivAt_shift_integral {W : ℂ → ℂ} (hW : Continuous W) {g : ℂ → ℂ} {s : ℝ}
    (hg : HolPer g s) {t : ℂ} (ht : t ∈ strip s) :
    HasDerivAt (fun z => ∫ σ in (0:ℝ)..2 * π, W σ * g (z + σ))
      (∫ σ in (0:ℝ)..2 * π, W σ * deriv g (t + σ)) t := by
  have h := hasDerivAt_intervalIntegral_of_holo (φ := fun σ z => W σ * g (z + σ))
    (isOpen_strip' s) (by positivity : (0:ℝ) ≤ 2 * π) ?_ ?_ ht
  · have e : ∀ σ : ℝ, deriv (fun z => W σ * g (z + σ)) t = W σ * deriv g (t + σ) := by
      intro σ
      have hg' : HasDerivAt g (deriv g (t + σ)) (t + σ) :=
        (hg.holo.differentiableAt ((isOpen_strip' s).mem_nhds
          (add_ofReal_mem_strip ht σ))).hasDerivAt
      exact ((hg'.comp_add_const t σ).const_mul (W σ)).deriv
    simpa only [e] using h
  · exact (hW.comp (Complex.continuous_ofReal.comp continuous_fst)).continuousOn.mul
      (hg.holo.continuousOn.comp (Continuous.continuousOn
        (f := fun p : ℝ × ℂ => p.2 + (p.1 : ℂ)) (by fun_prop))
        (fun p hp => add_ofReal_mem_strip hp.2 p.1))
  · intro σ _
    exact (hg.holo.comp (f := fun z => z + (σ : ℂ))
      ((differentiable_id.add_const _).differentiableOn)
      (fun z hz => add_ofReal_mem_strip hz σ)).const_mul (W σ)

lemma shift_integral_const {g : ℂ → ℂ} {s : ℝ} (hs : 0 < s) (hg : HolPer g s) {t : ℂ}
    (ht : t ∈ strip s) :
    ∫ σ in (0:ℝ)..2 * π, g (t + σ) = ∫ σ in (0:ℝ)..2 * π, g σ := by
  have hGd : ∀ z ∈ strip s,
      HasDerivAt (fun z => ∫ σ in (0:ℝ)..2 * π, g (z + σ)) 0 z := by
    intro z hz
    have h1 := hasDerivAt_shift_integral (W := fun _ => 1) continuous_const hg hz
    have h2 := ftc_shift (W := fun _ => 1) (W' := fun _ => 0)
      (fun z => hasDerivAt_const z 1) continuous_const hg hz
    simp only [one_mul, zero_mul, sub_self, intervalIntegral.integral_zero] at h1 h2
    rw [h2] at h1
    exact h1
  have := (isOpen_strip' s).is_const_of_deriv_eq_zero (isPreconnected_strip s)
    (fun z hz => (hGd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hGd z hz).deriv) ht (show (0:ℂ) ∈ strip s by simp [strip, hs])
  simpa using this

theorem solK_spec {κ : ℝ} (hκ : ∀ m : ℤ, κ ≠ m) {g : ℂ → ℂ} {s : ℝ} (hs : 0 < s)
    (hg : HolPer g s) :
    HolPer (solK κ g) s ∧
      ∀ t ∈ strip s, HasDerivAt (solK κ g) (g t - Complex.I * κ * solK κ g t) t := by
  have he : Complex.exp (2 * π * Complex.I * κ) - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    apply hκ n
    have h2 : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (κ : ℂ) = n := by
      apply mul_left_cancel₀ h2
      rw [hn]; ring
    exact_mod_cast this
  have key : ∀ t ∈ strip s, HasDerivAt (solK κ g) (g t - Complex.I * κ * solK κ g t) t := by
    intro t ht
    have h1 := (hasDerivAt_shift_integral (W := fun z => Complex.exp (Complex.I * κ * z))
      (by fun_prop) hg ht).const_mul (Complex.exp (2 * π * Complex.I * κ) - 1)⁻¹
    have h2 := ftc_shift (W := fun z => Complex.exp (Complex.I * κ * z))
      (W' := fun z => Complex.I * κ * Complex.exp (Complex.I * κ * z))
      (fun z => by
        have := ((hasDerivAt_id' z).const_mul (Complex.I * κ)).cexp
        convert this using 1
        ring)
      (by fun_prop) hg ht
    have hW2 : Complex.exp (Complex.I * κ * ((2 * π : ℝ) : ℂ)) =
        Complex.exp (2 * π * Complex.I * κ) := by
      congr 1; push_cast; ring
    simp only [hW2, mul_zero, Complex.exp_zero] at h2
    rw [h2] at h1
    convert h1 using 1
    · rfl
    have hI : ∫ σ in (0:ℝ)..2 * π,
        Complex.I * κ * Complex.exp (Complex.I * κ * σ) * g (t + σ) =
        Complex.I * κ * ∫ σ in (0:ℝ)..2 * π, Complex.exp (Complex.I * κ * σ) * g (t + σ) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun σ _ => ?_
      ring
    rw [hI]
    simp only [solK]
    linear_combination (-(g t)) * inv_mul_cancel₀ he
  refine ⟨⟨fun t ht => (key t ht).differentiableAt.differentiableWithinAt, fun t => ?_, ?_⟩, key⟩
  · simp only [solK]
    congr 1
    refine intervalIntegral.integral_congr fun σ _ => ?_
    rw [show t + 2 * π + σ = (t + σ) + 2 * π by ring, hg.per]
  · obtain ⟨B, hB⟩ := hg.bdd
    refine ⟨‖(Complex.exp (2 * π * Complex.I * κ) - 1)⁻¹‖ * (B * |2 * π - 0|),
      fun t ht => ?_⟩
    simp only [solK]
    rw [norm_mul]
    gcongr
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ _
    rw [norm_mul, show Complex.I * κ * σ = ((κ * σ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hB _ (add_ofReal_mem_strip ht σ)

theorem solK_conj (κ : ℝ) {g g' : ℂ → ℂ} (h : ∀ x : ℝ, g' x = conj (g x)) (t : ℝ) :
    conj (solK κ g t) = solK (-κ) g' t := by
  simp only [solK, map_mul, map_inv₀, map_sub, map_one]
  rw [← intervalIntegral.intervalIntegral_conj]
  congr 1
  · rw [← Complex.exp_conj]
    congr 3
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.ofReal_neg]
    ring
  · refine intervalIntegral.integral_congr fun σ _ => ?_
    simp only [map_mul, ← Complex.exp_conj]
    rw [← Complex.ofReal_add, h]
    congr 2
    simp [Complex.conj_ofReal]

theorem sol0_spec {g : ℂ → ℂ} {s : ℝ} (hs : 0 < s) (hg : HolPer g s) :
    HolPer (sol0 g) s ∧ ∀ t ∈ strip s, HasDerivAt (sol0 g) (g t - avg g) t := by
  have h2π : ((2 * π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have key : ∀ t ∈ strip s, HasDerivAt (sol0 g) (g t - avg g) t := by
    intro t ht
    have h1 := (hasDerivAt_shift_integral (W := fun z => z) continuous_id hg ht).const_mul
      ((2 * π : ℝ) : ℂ)⁻¹
    have h2 := ftc_shift (W := fun z => z) (W' := fun _ => 1) (fun z => hasDerivAt_id z)
      continuous_const hg ht
    simp only [one_mul, sub_zero] at h2
    rw [shift_integral_const hs hg ht] at h2
    rw [h2] at h1
    convert h1 using 1
    · rfl
    simp only [avg]
    field_simp
  refine ⟨⟨fun t ht => (key t ht).differentiableAt.differentiableWithinAt, fun t => ?_, ?_⟩, key⟩
  · simp only [sol0]
    congr 1
    refine intervalIntegral.integral_congr fun σ _ => ?_
    rw [show t + 2 * π + σ = (t + σ) + 2 * π by ring, hg.per]
  · obtain ⟨B, hB⟩ := hg.bdd
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp [strip, hs]))
    refine ⟨‖((2 * π : ℝ) : ℂ)⁻¹‖ * ((2 * π * B) * |2 * π - 0|), fun t ht => ?_⟩
    simp only [sol0]
    rw [norm_mul]
    gcongr
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    rw [uIoc_of_le (by positivity)] at hσ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ.1]
    exact mul_le_mul hσ.2 (hB _ (add_ofReal_mem_strip ht σ)) (norm_nonneg _) (by positivity)

theorem sol0_real {g : ℂ → ℂ} (h : ∀ x : ℝ, (g x).im = 0) :
    (∀ x : ℝ, (sol0 g x).im = 0) ∧ (avg g).im = 0 := by
  have hr : ∀ x : ℝ, g x = ((g x).re : ℂ) := fun x => Complex.ext (by simp) (by simp [h x])
  constructor
  · intro x
    have : ∫ σ in (0:ℝ)..2 * π, (σ : ℂ) * g (↑x + ↑σ) =
        ((∫ σ in (0:ℝ)..2 * π, σ * (g ↑(x + σ)).re : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun σ _ => ?_
      show (σ : ℂ) * g (↑x + ↑σ) = ((σ * (g ↑(x + σ)).re : ℝ) : ℂ)
      rw [Complex.ofReal_mul, ← hr, Complex.ofReal_add]
    rw [sol0, this, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_im]
  · have : ∫ σ in (0:ℝ)..2 * π, g σ = ((∫ σ in (0:ℝ)..2 * π, (g σ).re : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun σ _ => ?_
      exact hr σ
    rw [avg, this, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_im]

end ABC.S4.R3Aux
