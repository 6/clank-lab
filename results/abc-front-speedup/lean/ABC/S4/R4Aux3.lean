import ABC.S4.R4Aux2

/-! R4 helper: coordinates `v = (1/2, −i/2)` and the 3-jet of the period map. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

noncomputable section

namespace ABC.S4.R4Aux

def vR : C2 := ![1 / 2, -Complex.I / 2]

theorem ofW_vR (w : ℂ) : ofW vR w = !₂[w.re, w.im] := by
  ext i; fin_cases i <;> simp [ofW, vR]; ring

theorem toW_vR (y : E 2) : toW vR y = (y 0 : ℂ) + (y 1 : ℂ) * Complex.I := by
  simp only [toW, vR]
  simp
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

theorem norm_reim (w : ℂ) : ‖(!₂[w.re, w.im] : E 2)‖ = ‖w‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Complex.norm_def, Complex.normSq_apply]
  simp [sq]

-- `λ = e^{−2πiν}`
def lam (ν : ℝ) : ℂ := Complex.exp (-(2 * π * ν : ℝ) * Complex.I)

def ajet (ν b : ℝ) (j k : ℕ) : ℂ :=
  if j = 1 ∧ k = 0 then lam ν else if j = 2 ∧ k = 1 then -2 * π * Complex.I * b * lam ν else 0

theorem jetPoly_ajet (ν b : ℝ) (w : ℂ) :
    jetPoly (ajet ν b) w = lam ν * w + -2 * π * Complex.I * b * lam ν * w ^ 2 * conj w := by
  simp [jetPoly, ajet, Finset.sum_range_succ]

theorem norm_lam (ν : ℝ) : ‖lam ν‖ = 1 := by
  rw [lam, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

-- the rotation in the coordinate `w = x₀ + i x₁`
theorem g0_toC (ν b : ℝ) (x : E 2) (t : ℝ) :
    g0 ν b x t 0 + g0 ν b x t 1 * Complex.I =
      Complex.exp (-(om ν b x * t : ℝ) * Complex.I) * ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I]
  simp only [g0, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_toC_sub_le (y : E 2) (g : C2) :
    ‖((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) - (g 0 + g 1 * Complex.I)‖ ≤ 2 * ‖ofR y - g‖ := by
  have h0 : ‖(y 0 : ℂ) - g 0‖ ≤ ‖ofR y - g‖ := by simpa [ofR] using norm_le_pi_norm (ofR y - g) 0
  have h1 : ‖(y 1 : ℂ) - g 1‖ ≤ ‖ofR y - g‖ := by simpa [ofR] using norm_le_pi_norm (ofR y - g) 1
  have e : ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) - (g 0 + g 1 * Complex.I) =
      ((y 0 : ℂ) - g 0) + ((y 1 : ℂ) - g 1) * Complex.I := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one]
  linarith

/-- The truncated rotation: `‖e^{−2πi(ν+b|w|²)} w − jet‖ ≤ (2πb)² |w|⁵` for small `w`. -/
theorem rot_jet_le (ν b : ℝ) (w : ℂ) (hw : 2 * π * |b| * ‖w‖ ^ 2 ≤ 1) :
    ‖Complex.exp (-(om ν b !₂[w.re, w.im] * (2 * π) : ℝ) * Complex.I) * w -
        jetPoly (ajet ν b) w‖ ≤ (2 * π * |b|) ^ 2 * ‖w‖ ^ 5 := by
  set u : ℂ := -((2 * π * b * ‖w‖ ^ 2 : ℝ) : ℂ) * Complex.I
  have hom : (-(om ν b !₂[w.re, w.im] * (2 * π) : ℝ) : ℂ) * Complex.I =
      -(2 * π * ν : ℝ) * Complex.I + u := by
    have : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    simp only [u, om, this]
    simp
    ring
  have hconj : w ^ 2 * conj w = ((‖w‖ ^ 2 : ℝ) : ℂ) * w := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', sq]; ring
  have e : Complex.exp (-(om ν b !₂[w.re, w.im] * (2 * π) : ℝ) * Complex.I) * w -
      jetPoly (ajet ν b) w = lam ν * w * (Complex.exp u - 1 - u) := by
    rw [hom, Complex.exp_add, jetPoly_ajet, lam]
    simp only [u]
    rw [mul_assoc _ (w ^ 2), hconj]
    push_cast
    ring
  have hu : ‖u‖ = 2 * π * |b| * ‖w‖ ^ 2 := by
    simp only [u, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w‖ ^ 2), abs_of_pos pi_pos]
    norm_num
  rw [e, norm_mul, norm_mul, norm_lam, one_mul]
  have := Complex.norm_exp_sub_one_sub_id_le (x := u) (by rw [hu]; exact hw)
  rw [hu] at this
  calc ‖w‖ * ‖Complex.exp u - 1 - u‖ ≤ ‖w‖ * (2 * π * |b| * ‖w‖ ^ 2) ^ 2 := by gcongr
    _ = _ := by ring

theorem eventually_norm_lt (c : ℝ) (hc : 0 < c) : ∀ᶠ w : ℂ in 𝓝 0, ‖w‖ < c :=
  (continuous_norm.tendsto' (0 : ℂ) 0 norm_zero).eventually (gt_mem_nhds hc)

theorem isJet3_period {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ} {P' : E 2 → E 2} (hρ : 0 < ρ)
    (hs : 0 < s) (hK : IsTPHam (Kbnf ν b R) ρ s) (hR : Bound R ρ s C 5)
    (hP : IsPeriodMap (Kbnf ν b R) P' ρ) : IsJet3 P' 0 vR (ajet ν b) := by
  obtain ⟨δ, hδ, M, hM⟩ := period_est hρ hs hK hR hP
  unfold IsJet3
  refine IsBigO.trans_isLittleO (g := fun w : ℂ => ‖w‖ ^ 4) ?_
    (isLittleO_norm_pow_norm_pow (by norm_num))
  refine IsBigO.of_bound (2 * M + (2 * π * |b|) ^ 2) ?_
  have hη : 0 < 1 / (2 * π * |b| + 1) := by positivity
  filter_upwards [eventually_norm_lt δ hδ, eventually_norm_lt 1 one_pos,
    eventually_norm_lt _ hη] with w h1 h2 h3
  have hw0 := norm_nonneg w
  have h3' : 2 * π * |b| * ‖w‖ ^ 2 ≤ 1 := by
    have hA : 0 ≤ 2 * π * |b| := by positivity
    have : (2 * π * |b|) * ‖w‖ < 1 := by
      rw [lt_div_iff₀ (by positivity)] at h3
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : ‖w‖ ^ 2 ≤ ‖w‖) hA]
  simp only [zero_add, sub_zero, ofW_vR, toW_vR, norm_pow, norm_norm]
  set x : E 2 := !₂[w.re, w.im] with hxdef
  have hx : ‖x‖ = ‖w‖ := norm_reim w
  have hxw : (x 0 : ℂ) + (x 1 : ℂ) * Complex.I = w := by simp [x, Complex.re_add_im]
  have A := norm_toC_sub_le (P' x) (g0 ν b x (2 * π))
  rw [g0_toC, hxw] at A
  have B := rot_jet_le ν b w h3'
  have hMx := hM x (by rw [hx]; exact h1)
  rw [hx] at hMx
  have h5 : ‖w‖ ^ 5 ≤ ‖w‖ ^ 4 := pow_le_pow_of_le_one hw0 h2.le (by norm_num)
  calc _ ≤ ‖((P' x 0 : ℝ) : ℂ) + ((P' x 1 : ℝ) : ℂ) * Complex.I -
          Complex.exp (-(om ν b x * (2 * π) : ℝ) * Complex.I) * w‖ +
        ‖Complex.exp (-(om ν b x * (2 * π) : ℝ) * Complex.I) * w - jetPoly (ajet ν b) w‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * (M * ‖w‖ ^ 4) + (2 * π * |b|) ^ 2 * ‖w‖ ^ 4 := by
        gcongr
        · exact A.trans (by linarith)
        · exact B.trans (by gcongr)
    _ = _ := by ring

theorem lam_ne (ν : ℝ) (hnr : NonRes4 ν) :
    (lam ν).im ≠ 0 ∧ lam ν ^ 2 ≠ lam ν ∧ lam ν ^ 2 ≠ conj (lam ν) := by
  have hsq : lam ν ^ 2 = Complex.exp (-(2 * (2 * π * ν) : ℝ) * Complex.I) := by
    rw [lam, sq, ← Complex.exp_add]; push_cast; ring_nf
  have hcj : conj (lam ν) = Complex.exp ((2 * π * ν : ℝ) * Complex.I) := by
    rw [lam, ← Complex.exp_conj]; simp [map_ofNat]
  have hπ := pi_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [lam, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_im, Real.sin_neg, neg_ne_zero]
    intro h
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h
    exact hnr 2 (by norm_num) (by norm_num) n (by push_cast; nlinarith)
  · rw [hsq, lam]
    intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    have := congrArg Complex.im hn
    simp at this
    exact hnr 1 le_rfl (by norm_num) (-n) (by push_cast; nlinarith)
  · rw [hsq, hcj]
    intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    have := congrArg Complex.im hn
    simp at this
    exact hnr 3 (by norm_num) (by norm_num) (-n) (by push_cast; nlinarith)

theorem twistData_period {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ} {P' : E 2 → E 2} (hρ : 0 < ρ)
    (hs : 0 < s) (hK : IsTPHam (Kbnf ν b R) ρ s) (hR : Bound R ρ s C 5) (hnr : NonRes4 ν)
    (hP : IsPeriodMap (Kbnf ν b R) P' ρ) : TwistData P' 0 vR (ajet ν b) := by
  obtain ⟨h1, h2, h3⟩ := lam_ne ν hnr
  refine ⟨?_, isJet3_period hρ hs hK hR hP, by simp [ajet], by simp [ajet], ?_, ?_, ?_⟩
  · simp [vR, map_ofNat]
  · simpa [ajet] using h1
  · simpa [ajet] using h2
  · simpa [ajet] using h3

theorem beta_ajet (ν b : ℝ) :
    birkhoffBeta (ajet ν b) = -2 * π * Complex.I * b * ajet ν b 1 0 := by
  simp [birkhoffBeta, ajet]

end ABC.S4.R4Aux
