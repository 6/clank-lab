import ABC.S4.TwistConjAux3

/-! T1 helpers: derivatives in the coordinate `w`, `jdet = |λ|²`, and the conjugacy step. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

set_option linter.unusedSimpArgs false

noncomputable section

namespace ABC.S4.TwistConjAux

open ABC

/-- the linear part `w ↦ c₁₀ w + c₀₁ w̄` of a jet -/
def lin (c : ℕ → ℕ → ℂ) : ℂ →L[ℝ] ℂ :=
  c 1 0 • ContinuousLinearMap.id ℝ ℂ + c 0 1 • Complex.conjCLE.toContinuousLinearMap

theorem lin_apply (c : ℕ → ℕ → ℂ) (w : ℂ) : lin c w = c 1 0 * w + c 0 1 * conj w := by
  simp [lin]

theorem hasFDerivAt_of_jet {F : ℂ → ℂ} {c : ℕ → ℕ → ℂ}
    (hF : (fun w => F w - jetPoly c w) =o[𝓝 0] fun w => ‖w‖ ^ 3) (hc0 : c 0 0 = 0) :
    HasFDerivAt F (lin c) 0 := by
  have hF0 : F 0 = 0 := (jet_val (n := 2) hF).trans hc0
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h1 : (fun w => F w - jetPoly c w) =o[𝓝 0] fun w => ‖w‖ ^ 1 :=
    hF.trans_isBigO (pow_isBigO (by norm_num))
  have h2 : BO 2 (fun w => jetPoly c w - lin c w) := by
    have q2 := ((BO_mono_ (c 2 0) 2 0).add (BO_mono_ (c 1 1) 1 1)).add (BO_mono_ (c 0 2) 0 2)
    have q3 := (((BO_mono_ (c 3 0) 3 0).add (BO_mono_ (c 2 1) 2 1)).add
      (BO_mono_ (c 1 2) 1 2)).add (BO_mono_ (c 0 3) 0 3)
    refine (q2.add (BO.mono (by norm_num : 2 ≤ 3) q3)).congr fun w => ?_
    rw [jetPoly_eq, lin_apply, hc0]; ring
  have := h1.add (h2.isLittleO (m := 1) (by norm_num))
  refine isLittleO_norm_right.1 ?_
  simp only [pow_one] at this
  refine this.congr_left fun w => ?_
  rw [zero_add, hF0]; ring

theorem ofW_zero (v : C2) : ofW v 0 = 0 := by
  ext i; apply Complex.ofReal_injective; simp [ofW_apply]

theorem coord_hasFDerivAt {f : E 2 → E 2} {p q : E 2} {v v' : C2}
    (hv : (v 0 * conj (v 1)).im ≠ 0) (hv' : (v' 0 * conj (v' 1)).im ≠ 0)
    (hf : DifferentiableAt ℝ f p) :
    HasFDerivAt (fun w => toW v' (f (p + ofW v w) - q))
      (((ofWC v' hv').symm : E 2 →L[ℝ] ℂ).comp
        ((fderiv ℝ f p).comp ((ofWC v hv : ℂ →L[ℝ] E 2)))) 0 := by
  have h1 : HasFDerivAt (fun w => p + ofWC v hv w) (ofWC v hv : ℂ →L[ℝ] E 2) 0 :=
    (ofWC v hv).hasFDerivAt.const_add p
  have h2 : HasFDerivAt f (fderiv ℝ f p) (p + ofWC v hv 0) := by
    rw [map_zero, add_zero]; exact hf.hasFDerivAt
  have h3 := ((h2.comp (0 : ℂ) h1).sub_const q)
  exact (ofWC v' hv').symm.hasFDerivAt.comp (0 : ℂ) h3

/-- the linear part of the map in the coordinate `w` is `λ w` -/
theorem jet_linear {f : E 2 → E 2} {p : E 2} {v : C2} {a : ℕ → ℕ → ℂ}
    (hd : TwistData f p v a) (hf : DifferentiableAt ℝ f p) (w : ℂ) :
    toW v (fderiv ℝ f p (ofW v w)) = a 1 0 * w := by
  have h1 := coord_hasFDerivAt (q := p) hd.indep hd.indep hf
  have h2 := hasFDerivAt_of_jet hd.jet hd.fixed
  have := congrArg (fun L : ℂ →L[ℝ] ℂ => L w) (h1.unique h2)
  simpa [lin_apply, hd.diag] using this

theorem jdet_eq {f : E 2 → E 2} {p : E 2} {v : C2} {a : ℕ → ℕ → ℂ}
    (hd : TwistData f p v a) (hf : DifferentiableAt ℝ f p) :
    jdet f p = Complex.normSq (a 1 0) := by
  set e := ofWE v hd.indep
  have hA : (fderiv ℝ f p : E 2 →ₗ[ℝ] E 2) =
      (e : ℂ →ₗ[ℝ] E 2) ∘ₗ Algebra.lmul ℝ ℂ (a 1 0) ∘ₗ (e.symm : E 2 →ₗ[ℝ] ℂ) := by
    ext1 x
    have := jet_linear hd hf (toW v x)
    rw [ofW_toW hd.indep] at this
    change fderiv ℝ f p x = ofW v (a 1 0 * toW v x)
    rw [← this, ofW_toW hd.indep]
  rw [jdet, hA, LinearMap.det_conj, ← Algebra.norm_apply, Algebra.norm_complex_apply]


/-! ### the conjugacy step -/

/-- real and imaginary parts of `v` -/
def reV (v : C2) : E 2 := !₂[(v 0).re, (v 1).re]

def imV (v : C2) : E 2 := !₂[(v 0).im, (v 1).im]

theorem ofW_eq_smul (v : C2) (w : ℂ) : ofW v w = (2 * w.re) • reV v - (2 * w.im) • imV v := by
  ext i; fin_cases i <;> simp [ofW, reV, imV, Complex.mul_re] <;> ring

/-- the complexified image `A v` -/
def pushV (A : E 2 →L[ℝ] E 2) (v : C2) : C2 :=
  fun i => ((A (reV v) i : ℝ) : ℂ) + ((A (imV v) i : ℝ) : ℂ) * Complex.I

theorem ofW_pushV (A : E 2 →L[ℝ] E 2) (v : C2) (w : ℂ) : ofW (pushV A v) w = A (ofW v w) := by
  have h1 : reV (pushV A v) = A (reV v) := by
    ext i; fin_cases i <;> simp [reV, pushV]
  have h2 : imV (pushV A v) = A (imV v) := by
    ext i; fin_cases i <;> simp [imV, pushV]
  rw [ofW_eq_smul, ofW_eq_smul, h1, h2, map_sub, map_smul, map_smul]

theorem indep_of_inj {u : C2} (hu : ∀ w, ofW u w = 0 → w = 0) : (u 0 * conj (u 1)).im ≠ 0 := by
  intro h0
  have key : ∀ w, (u 0 * w).re = 0 → (u 1 * w).re = 0 → w = 0 := fun w h1 h2 =>
    hu w (by ext i; fin_cases i <;> simp [ofW, h1, h2])
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
  by_cases hz : u 0 = 0
  · by_cases hz' : u 1 = 0
    · exact one_ne_zero (key 1 (by simp [hz]) (by simp [hz']))
    · have := key (Complex.I * conj (u 1)) (by simp [hz])
        (by simp [Complex.mul_re, Complex.mul_im]; ring)
      simp [hz'] at this
  · have := key (Complex.I * conj (u 0)) (by simp [Complex.mul_re, Complex.mul_im]; ring)
      (by simp [Complex.mul_re, Complex.mul_im]; linarith)
    simp [hz] at this

theorem toW_zero (v : C2) : toW v 0 = 0 := by simp [toW]

theorem conj_core {f₁ f₂ h : E 2 → E 2} {p : E 2} (hh : ContDiffAt ℝ 3 h p)
    (hh' : (fderiv ℝ h p).ker = ⊥) (hf : ContDiffAt ℝ 3 f₁ p) (hdet : jdet f₁ p = 1)
    (hc : ∀ᶠ x in 𝓝 p, f₂ (h x) = h (f₁ x)) {v : C2} {a : ℕ → ℕ → ℂ}
    (hd : TwistData f₁ p v a) :
    ∃ v₂ b, TwistData f₂ (h p) v₂ b ∧ birkhoffBeta b = birkhoffBeta a := by
  have hv := hd.indep
  set Dh := fderiv ℝ h p with hDh
  -- `f₁` fixes `p`
  have hG0 := jet_val (n := 2) hd.jet
  have hfp : f₁ p = p := by
    rw [hd.fixed, ofW_zero, add_zero] at hG0
    have := congrArg (ofW v) hG0
    rw [ofW_toW hv, ofW_zero] at this
    exact sub_eq_zero.1 this
  -- a local inverse of `h`
  have hinj : Function.Injective Dh := LinearMap.ker_eq_bot.1 hh'
  have hsurj : Dh.range = ⊤ :=
    LinearMap.range_eq_top.2 (LinearMap.injective_iff_surjective.1 hinj)
  set De := ContinuousLinearEquiv.ofBijective Dh hh' hsurj
  have hhd : HasFDerivAt h (De : E 2 →L[ℝ] E 2) p := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact (hh.differentiableAt (by norm_num)).hasFDerivAt
  have hs := hh.hasStrictFDerivAt' hhd (by norm_num)
  have hg : ContDiffAt ℝ 3 (hs.localInverse h De p) (h p) := hh.to_localInverse hhd (by norm_num)
  have hgp : hs.localInverse h De p (h p) = p := hs.localInverse_apply_image
  have heq : f₂ =ᶠ[𝓝 (h p)] fun y => h (f₁ (hs.localInverse h De p y)) := by
    filter_upwards [hs.eventually_right_inverse, hs.localInverse_tendsto.eventually hc]
      with y hy1 hy2
    rw [hy1] at hy2
    exact hy2
  have hf₂ : ContDiffAt ℝ 3 f₂ (h p) := by
    have h1 : ContDiffAt ℝ 3 (fun y => f₁ (hs.localInverse h De p y)) (h p) := by
      have := hf; rw [← hgp] at this; exact this.comp (h p) hg
    have h2 : ContDiffAt ℝ 3 (fun y => h (f₁ (hs.localInverse h De p y))) (h p) := by
      have := hh; rw [← hfp, ← hgp] at this; exact this.comp (h p) h1
    exact h2.congr_of_eventuallyEq heq
  -- the new eigenvector
  set v₂ := pushV Dh v
  have hofW2 : ∀ w, ofW v₂ w = Dh (ofW v w) := ofW_pushV Dh v
  have hv₂ : (v₂ 0 * conj (v₂ 1)).im ≠ 0 := indep_of_inj fun w hw => by
    rw [hofW2] at hw
    have h0 : ofW v w = 0 := hinj (hw.trans (map_zero Dh).symm)
    rw [← toW_ofW hv w, h0, toW_zero]
  -- the three maps in coordinates
  set H : ℂ → ℂ := fun w => toW v₂ (h (p + ofW v w) - h p) with hH
  set G₁ : ℂ → ℂ := fun w => toW v (f₁ (p + ofW v w) - p) with hG₁
  set G₂ : ℂ → ℂ := fun z => toW v₂ (f₂ (h p + ofW v₂ z) - h p) with hG₂
  have haff : ∀ (q : E 2) (u : C2) (hu : (u 0 * conj (u 1)).im ≠ 0),
      ContDiffAt ℝ 3 (fun w => q + ofW u w) 0 := fun q u hu =>
    contDiffAt_const.add ((ofWC u hu : ℂ →L[ℝ] E 2).contDiff.contDiffAt)
  have hHd : ContDiffAt ℝ 3 H 0 := by
    have h1 := hh; rw [← add_zero p, ← ofW_zero v] at h1
    exact ((ofWC v₂ hv₂).symm : E 2 →L[ℝ] ℂ).contDiff.contDiffAt.comp (0 : ℂ)
      ((h1.comp (0 : ℂ) (haff p v hv)).sub contDiffAt_const)
  have hG₂d : ContDiffAt ℝ 3 G₂ 0 := by
    have h1 := hf₂; rw [← add_zero (h p), ← ofW_zero v₂] at h1
    exact ((ofWC v₂ hv₂).symm : E 2 →L[ℝ] ℂ).contDiff.contDiffAt.comp (0 : ℂ)
      ((h1.comp (0 : ℂ) (haff (h p) v₂ hv₂)).sub contDiffAt_const)
  obtain ⟨η, hη⟩ := taylor 3 le_rfl hHd
  obtain ⟨b, hb⟩ := taylor 3 le_rfl hG₂d
  -- `η` is tangent to the identity
  have hη0 : η 0 0 = 0 := by
    rw [← jet_val (n := 2) hη]; simp [H, ofW_zero, toW_zero]
  have hlin : ∀ w, lin η w = w := by
    have h1 := coord_hasFDerivAt (q := h p) hv hv₂ (hh.differentiableAt (by norm_num))
    have h2 := hasFDerivAt_of_jet hη hη0
    intro w
    have := congrArg (fun L : ℂ →L[ℝ] ℂ => L w) (h2.unique h1)
    simp only at this
    rw [this]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      ofWC_apply, ofWC_symm_apply]
    rw [← hDh, ← hofW2, toW_ofW hv₂]
  have l1 := hlin 1
  have l2 := hlin Complex.I
  rw [lin_apply] at l1 l2
  simp only [map_one, mul_one, Complex.conj_I] at l1 l2
  have hη10 : η 1 0 = 1 := by
    linear_combination (1 / 2 : ℂ) * l1 + (-Complex.I / 2) * l2
      + (η 1 0 - η 0 1 - 1) / 2 * Complex.I_sq
  have hη01 : η 0 1 = 0 := by
    linear_combination (1 / 2 : ℂ) * l1 + (Complex.I / 2) * l2
      - (η 1 0 - η 0 1 - 1) / 2 * Complex.I_sq
  -- the conjugacy in coordinates
  have hrel : (fun w => G₂ (H w)) =ᶠ[𝓝 0] fun w => H (G₁ w) := by
    have ht : Tendsto (fun w : ℂ => p + ofW v w) (𝓝 0) (𝓝 p) := by
      have hc' : Continuous (fun w : ℂ => p + ofWC v hv w) :=
        continuous_const.add (ofWC v hv).continuous
      have := hc'.tendsto (0 : ℂ)
      simpa [ofW_zero] using this
    filter_upwards [ht.eventually hc] with w hw
    simp only [H, G₁, G₂]
    rw [ofW_toW hv₂, ofW_toW hv, add_sub_cancel, add_sub_cancel, hw]
  have j1 := comp_jet hη0 hη01 hη hb
  have j2 := comp_jet hd.fixed hd.diag hd.jet hη
  have E := jet_eq hrel j1 j2
  have hL : a 1 0 * conj (a 1 0) = 1 := by
    rw [Complex.mul_conj, ← jdet_eq hd (hf.differentiableAt (by norm_num)), hdet]
    simp
  obtain ⟨b00, b10, b01, hβ⟩ := beta_tangent hη0 hη01 hη10 hL hd.nonreal hd.nonres E
  exact ⟨v₂, b, ⟨hv₂, hb, b00, b01, b10 ▸ hd.nonreal, b10 ▸ hd.nonres⟩, hβ⟩

end ABC.S4.TwistConjAux
