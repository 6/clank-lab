import ABC.S4.Defs

/-! Helpers for `R6_hyps` (`ABC/S4/R6.lean`). -/

open Set Metric Filter Topology Real
open ABC.Poschel2001 (Pt Ph DO Drs Oh OmegaAlpha ofRe imPart twoPiE IsRealAnalyticOn)

noncomputable section

namespace ABC.S4.R6Aux

open ABC ABC.S4

theorem omegaE_isOpen (ν b ε : ℝ) (hb : b ≠ 0) : IsOpen (OmegaE ν b ε) := by
  have hS : IsOpen {ω : Fin 2 → ℝ | ω 1 ∈ Ioo (1 / 2 : ℝ) (3 / 2)} :=
    isOpen_Ioo.preimage (continuous_apply 1)
  have hc : ContinuousOn (fun ω : Fin 2 → ℝ => (ω 0 / ω 1 - ν) / (2 * b))
      {ω : Fin 2 → ℝ | ω 1 ∈ Ioo (1 / 2 : ℝ) (3 / 2)} := by
    intro ω hω
    have h1 : ω 1 ≠ 0 := by have := hω.1; positivity
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  convert hc.isOpen_inter_preimage hS (isOpen_Ioo (a := ε / 2) (b := ε)) using 1
  ext ω
  simp only [OmegaE, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, abs_sub_lt_iff]
  constructor
  · rintro ⟨h1, P, hP, hω⟩
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rw [hω, show ν + 2 * b * P - ν = P * (2 * b) by ring, mul_div_assoc,
      div_self (by positivity), mul_one]
    exact hP
  · rintro ⟨h1, hP⟩
    refine ⟨⟨by linarith, by linarith⟩, _, hP, ?_⟩
    field_simp
    ring

theorem omegaE_isConnected (ν b ε : ℝ) (hε : 0 < ε) :
    IsConnected (OmegaE ν b ε) := by
  have e : OmegaE ν b ε = (fun q : ℝ × ℝ => (![q.1 * (ν + 2 * b * q.2), q.1] : Fin 2 → ℝ)) ''
      (Ioo (1 / 2 : ℝ) (3 / 2) ×ˢ Ioo (ε / 2) ε) := by
    ext ω
    simp only [OmegaE, mem_ofPred_eq, mem_image, mem_prod, Prod.exists, abs_sub_lt_iff]
    constructor
    · rintro ⟨h1, P, hP, hω⟩
      have h1' : ω 1 ≠ 0 := by intro h; rw [h] at h1; norm_num at h1
      refine ⟨ω 1, P, ⟨⟨by linarith, by linarith⟩, hP⟩, ?_⟩
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [← hω]; field_simp
      · simp
    · rintro ⟨a, P, ⟨ha, hP⟩, rfl⟩
      have ha' : a ≠ 0 := by have := ha.1; positivity
      refine ⟨⟨by simp; linarith [ha.2], by simp; linarith [ha.1]⟩, P, hP, ?_⟩
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp
  rw [e]
  refine ((isConnected_Ioo (by norm_num)).prod (isConnected_Ioo (by linarith))).image _ ?_
  apply Continuous.continuousOn
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

/-- `ε ^ (k / 8) = δ ^ k` with `δ = ε ^ (1 / 8)`. -/
theorem rpow_eighths {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    ε ^ ((k : ℝ) / 8) = (ε ^ (1 / 8 : ℝ)) ^ k := by
  rw [← Real.rpow_mul_natCast hε]; ring_nf

theorem norm_cos_le (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h := congrArg norm (Complex.two_cos (x := z))
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at h
  have h2 := norm_add_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
  rw [Complex.norm_exp, Complex.norm_exp] at h2
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, mul_zero,
    mul_one, zero_sub, neg_neg] at h2
  have e1 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  have e2 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  linarith

theorem norm_sin_le (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h := congrArg norm (Complex.two_sin (x := z))
  rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num, Complex.norm_I, mul_one] at h
  have h2 := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
  rw [Complex.norm_exp, Complex.norm_exp] at h2
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, mul_zero,
    mul_one, zero_sub, neg_neg] at h2
  have e1 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  have e2 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  linarith

theorem norm_polarW_le {P θ : ℂ} {B : ℝ} (hB : 0 ≤ B) (hP : ‖2 * P‖ ≤ B ^ 2) :
    ‖polarW P θ‖ ≤ B * Real.exp |θ.im| := by
  have hc : ‖(2 * P) ^ (1 / 2 : ℂ)‖ ≤ B := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real]
    calc ‖2 * P‖ ^ (1 / 2 : ℝ) ≤ (B ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (norm_nonneg _) hP (by norm_num)
      _ = B := by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hB]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  fin_cases i
  · show ‖(2 * P) ^ (1 / 2 : ℂ) * Complex.cos θ‖ ≤ _
    rw [norm_mul]; exact mul_le_mul hc (norm_cos_le θ) (norm_nonneg _) hB
  · show ‖-((2 * P) ^ (1 / 2 : ℂ) * Complex.sin θ)‖ ≤ _
    rw [norm_neg, norm_mul]; exact mul_le_mul hc (norm_sin_le θ) (norm_nonneg _) hB

/-- A Lipschitz constant of `p0` near the real points of `OmegaE`. -/
def M (ν b : ℝ) : ℝ := 6 * (1 + |ν| + 2 * |b|) / |b|

theorem M_nonneg (ν b : ℝ) : 0 ≤ M ν b := by unfold M; positivity

theorem p0_ofRe_mem {ν b ε : ℝ} (hb : b ≠ 0) {a : Fin 2 → ℝ} (ha : a ∈ OmegaE ν b ε) :
    ∃ P ∈ Ioo (ε / 2) ε, p0 ν b (ofRe a) = (P : ℂ) := by
  obtain ⟨-, P, hP, h⟩ := ha
  refine ⟨P, hP, ?_⟩
  simp only [p0, ofRe]
  rw [show ((a 0 : ℂ) / (a 1 : ℂ)) = ((a 0 / a 1 : ℝ) : ℂ) by push_cast; rfl, h]
  have : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  push_cast
  field_simp
  ring

theorem p0_near {ν b ε h : ℝ} (hb : b ≠ 0) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hh : h ≤ 1 / 4)
    {a : Fin 2 → ℝ} (ha : a ∈ OmegaE ν b ε) {ω : C2} (hω : ‖ω - ofRe a‖ < h) :
    ω 1 ≠ 0 ∧ ‖ω 1‖ ≤ 2 ∧ ‖p0 ν b ω - p0 ν b (ofRe a)‖ ≤ M ν b * h := by
  obtain ⟨ha1, P, hP, hrel⟩ := ha
  rw [abs_sub_lt_iff] at ha1
  have hd : ∀ i, ‖ω i - (a i : ℂ)‖ < h := fun i =>
    lt_of_le_of_lt (norm_le_pi_norm (ω - ofRe a) i) hω
  have hh0 : 0 < h := lt_of_le_of_lt (norm_nonneg _) hω
  have a1lo : 1 / 2 < a 1 := by linarith
  have a1hi : a 1 < 3 / 2 := by linarith
  have e1 : ‖((a 1 : ℝ) : ℂ)‖ = a 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have t1 := norm_sub_norm_le ((a 1 : ℝ) : ℂ) (ω 1)
  have t2 := norm_sub_norm_le (ω 1) ((a 1 : ℝ) : ℂ)
  rw [norm_sub_rev, e1] at t1
  rw [e1] at t2
  have hd1 := hd 1
  have hω1lo : 1 / 4 ≤ ‖ω 1‖ := by linarith
  have hω1 : ω 1 ≠ 0 := by intro h0; rw [h0, norm_zero] at hω1lo; norm_num at hω1lo
  refine ⟨hω1, by linarith, ?_⟩
  have ha1' : a 1 ≠ 0 := by positivity
  have ha0 : a 0 = a 1 * (ν + 2 * b * P) := by rw [← hrel]; field_simp
  have hA : |a 0| ≤ 3 / 2 * (|ν| + 2 * |b|) := by
    have hb' : |ν + 2 * b * P| ≤ |ν| + 2 * |b| := by
      calc |ν + 2 * b * P| ≤ |ν| + |2 * b * P| := abs_add_le _ _
        _ = |ν| + 2 * |b| * P := by
          rw [abs_mul, abs_mul, abs_of_pos (by linarith [hP.1] : 0 < P)]; norm_num
        _ ≤ |ν| + 2 * |b| := by nlinarith [abs_nonneg b, hP.2]
    rw [ha0, abs_mul, abs_of_pos (by linarith : 0 < a 1)]
    nlinarith [abs_nonneg (ν + 2 * b * P), abs_nonneg ν, abs_nonneg b]
  have key : p0 ν b ω - p0 ν b (ofRe a) =
      ((ω 0 - a 0) * a 1 - a 0 * (ω 1 - a 1)) / (ω 1 * a 1 * (2 * b)) := by
    simp only [p0, ofRe]
    have : (a 1 : ℂ) ≠ 0 := by exact_mod_cast ha1'
    have : (b : ℂ) ≠ 0 := by exact_mod_cast hb
    field_simp
    ring
  have hbpos : 0 < |b| := abs_pos.mpr hb
  have hden : |b| / 4 ≤ ‖ω 1 * (a 1 : ℂ) * (2 * b)‖ := by
    rw [norm_mul, norm_mul, e1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show ‖(2 : ℂ)‖ = 2 by norm_num]
    have : 1 / 4 * (1 / 2) ≤ ‖ω 1‖ * a 1 := by
      apply mul_le_mul hω1lo a1lo.le (by norm_num) (norm_nonneg _)
    nlinarith
  have hnum : ‖(ω 0 - a 0) * a 1 - a 0 * (ω 1 - a 1)‖ ≤ 3 / 2 * h * (1 + |ν| + 2 * |b|) := by
    calc _ ≤ ‖(ω 0 - a 0) * a 1‖ + ‖(a 0 : ℂ) * (ω 1 - a 1)‖ := norm_sub_le _ _
      _ = ‖ω 0 - a 0‖ * a 1 + |a 0| * ‖ω 1 - a 1‖ := by
          rw [norm_mul, norm_mul, e1, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ h * (3 / 2) + 3 / 2 * (|ν| + 2 * |b|) * h :=
          add_le_add (mul_le_mul (hd 0).le a1hi.le (by linarith) hh0.le)
            (mul_le_mul hA (hd 1).le (norm_nonneg _) (by positivity))
      _ = _ := by ring
  rw [key, norm_div]
  calc _ ≤ 3 / 2 * h * (1 + |ν| + 2 * |b|) / (|b| / 4) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = M ν b * h := by unfold M; field_simp; ring

theorem dom_facts {ν b ε s δ r α h : ℝ} (hb : b ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hδM : (M ν b + 1) * δ ≤ 1 / 4) (hε : ε = δ ^ 8) (hr : r = δ ^ 10) (hh : h ≤ δ ^ 9)
    {x : Pt 2} (hx : x ∈ DO r s (OmegaAlpha 2 (OmegaE ν b ε) α) h) :
    x.2.2 1 ≠ 0 ∧ ‖x.2.2 1‖ ≤ 2 ∧ ‖x.1 0‖ < δ ^ 10 ∧ 0 < (p0 ν b x.2.2 + x.1 0).re ∧
      ‖p0 ν b x.2.2 + x.1 0‖ ≤ 2 * δ ^ 8 ∧ |(x.2.1 0).im| < s ∧ |(x.2.1 1).im| < s := by
  obtain ⟨⟨hI, hθ⟩, a, ha, hω⟩ := hx
  have ha' : a ∈ OmegaE ν b ε := ha.1
  have hδ1' : δ ≤ 1 := by linarith
  have p8 : δ ^ 8 ≤ 1 := pow_le_one₀ hδ.le hδ1'
  have p9 : δ ^ 9 ≤ 1 / 4 := by
    calc δ ^ 9 ≤ (1 / 2) ^ 9 := pow_le_pow_left₀ hδ.le hδ1 9
      _ ≤ 1 / 4 := by norm_num
  obtain ⟨h1, h2, h3⟩ := p0_near hb (by rw [hε]; positivity) (by rw [hε]; exact p8)
    (hh.trans p9) ha' hω
  obtain ⟨P, hP, hP0⟩ := p0_ofRe_mem hb ha'
  rw [hε] at hP
  have hI0 : ‖x.1 0‖ < δ ^ 10 := (norm_le_pi_norm x.1 0).trans_lt (hr ▸ hI)
  have hd : ‖p0 ν b x.2.2 + x.1 0 - P‖ ≤ δ ^ 8 / 4 := by
    have e : p0 ν b x.2.2 + x.1 0 - P = (p0 ν b x.2.2 - p0 ν b (ofRe a)) + x.1 0 := by
      rw [hP0]; ring
    rw [e]
    have hM := M_nonneg ν b
    calc _ ≤ ‖p0 ν b x.2.2 - p0 ν b (ofRe a)‖ + ‖x.1 0‖ := norm_add_le _ _
      _ ≤ M ν b * δ ^ 9 + δ ^ 10 :=
          add_le_add (h3.trans (mul_le_mul_of_nonneg_left hh hM)) hI0.le
      _ = δ ^ 8 * (M ν b * δ + δ * δ) := by ring
      _ ≤ δ ^ 8 * (1 / 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
      _ = δ ^ 8 / 4 := by ring
  have hre := Complex.abs_re_le_norm (p0 ν b x.2.2 + x.1 0 - P)
  rw [Complex.sub_re, Complex.ofReal_re] at hre
  have hPn : ‖(P : ℂ)‖ = P := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [hP.1, pow_pos hδ 8])]
  have himθ : ∀ i, |(x.2.1 i).im| < s := fun i =>
    lt_of_le_of_lt (norm_le_pi_norm (imPart x.2.1) i) hθ
  refine ⟨h1, h2, hI0, ?_, ?_, himθ 0, himθ 1⟩
  · have := (abs_le.1 hre).1
    linarith [hP.1, pow_pos hδ 8]
  · have := norm_add_le (p0 ν b x.2.2 + x.1 0 - P) (P : ℂ)
    rw [sub_add_cancel, hPn] at this
    linarith [hP.2, pow_pos hδ 8]

theorem polydisc_isOpen (ρ : ℝ) : IsOpen (polydisc ρ) := by
  have : polydisc ρ = ball (0 : C2) ρ := by ext w; simp [polydisc]
  rw [this]; exact isOpen_ball

theorem strip_isOpen (s : ℝ) : IsOpen (strip s) :=
  isOpen_lt (by fun_prop) continuous_const

theorem R_holo {ν b ρ s : ℝ} {R : C2 → ℂ → ℂ} (hH : IsTPHam (Kbnf ν b R) ρ s) :
    DifferentiableOn ℂ (fun q : C2 × ℂ => R q.1 q.2) (polydisc ρ ×ˢ strip s) := by
  have e : (fun q : C2 × ℂ => R q.1 q.2) = fun q => Kbnf ν b R q.1 q.2 -
      ((ν : ℂ) / 2 * (q.1 0 ^ 2 + q.1 1 ^ 2) + (b : ℂ) / 4 * (q.1 0 ^ 2 + q.1 1 ^ 2) ^ 2) := by
    funext q; simp only [Kbnf]; ring
  rw [e]
  exact hH.holo.sub (Differentiable.differentiableOn (by fun_prop))

theorem R_per {ν b ρ s : ℝ} {R : C2 → ℂ → ℂ} (hH : IsTPHam (Kbnf ν b R) ρ s) (w : C2) (t : ℂ) :
    R w (t + 2 * π) = R w t := by
  have := hH.per w t
  simp only [Kbnf] at this
  exact add_left_cancel this

theorem pertP_diffAt {ν b ρ s : ℝ} {R : C2 → ℂ → ℂ}
    (hR : DifferentiableOn ℂ (fun q : C2 × ℂ => R q.1 q.2) (polydisc ρ ×ˢ strip s)) {x : Pt 2}
    (h1 : x.2.2 1 ≠ 0) (hre : 0 < (p0 ν b x.2.2 + x.1 0).re)
    (hw : polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0) ∈ polydisc ρ) (ht : x.2.1 1 ∈ strip s) :
    DifferentiableAt ℂ (pertP ν b R) x := by
  have hopen : IsOpen (polydisc ρ ×ˢ strip s) := (polydisc_isOpen ρ).prod (strip_isOpen s)
  have hRat : DifferentiableAt ℂ (fun q : C2 × ℂ => R q.1 q.2)
      (polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0), x.2.1 1) :=
    hR.differentiableAt (hopen.mem_nhds ⟨hw, ht⟩)
  have hp0 : DifferentiableAt ℂ (fun x : Pt 2 => p0 ν b x.2.2 + x.1 0) x := by
    unfold p0; fun_prop (disch := assumption)
  have hslit : 2 * (p0 ν b x.2.2 + x.1 0) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left
    rw [show (2 * (p0 ν b x.2.2 + x.1 0)).re = 2 * (p0 ν b x.2.2 + x.1 0).re by simp]
    linarith
  have hsq : DifferentiableAt ℂ (fun x : Pt 2 => (2 * (p0 ν b x.2.2 + x.1 0)) ^ (1 / 2 : ℂ)) x :=
    (hp0.const_mul 2).cpow_const hslit
  have hθ0 : DifferentiableAt ℂ (fun x : Pt 2 => x.2.1 0) x := by fun_prop
  have hW : DifferentiableAt ℂ (fun x : Pt 2 => polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0)) x := by
    rw [differentiableAt_pi]; intro i; fin_cases i
    · exact hsq.mul hθ0.ccos
    · exact (hsq.mul hθ0.csin).neg
  have hg : DifferentiableAt ℂ
      (fun x : Pt 2 => (polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0), x.2.1 1)) x :=
    hW.prodMk (by fun_prop)
  have hcomp := hRat.comp x hg
  have hω1 : DifferentiableAt ℂ (fun x : Pt 2 => x.2.2 1) x := by fun_prop
  have hb : DifferentiableAt ℂ (fun x : Pt 2 => (b : ℂ) * x.1 0 ^ 2) x := by fun_prop
  exact hω1.mul (hb.add hcomp)

theorem pertP_real {p : E 2} {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ}
    {h₀ : OpenPartialHomeomorph (E 2) (E 2)} {P' : E 2 → E 2} (h : BNF p ν b R ρ s C h₀ P')
    (I θ ω : Fin 2 → ℝ) (hre : 0 < (p0 ν b (ofRe ω) + ofRe I 0).re)
    (hw : ‖polarW (p0 ν b (ofRe ω) + ofRe I 0) (ofRe θ 0)‖ < ρ) :
    (pertP ν b R (ofRe I, ofRe θ, ofRe ω)).im = 0 := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (ω 0 / ω 1 - ν) / (2 * b) + I 0 := ⟨_, rfl⟩
  have hP : p0 ν b (ofRe ω) + ofRe I 0 = (q : ℂ) := by
    simp only [p0, ofRe, hq]; push_cast; ring
  rw [hP, Complex.ofReal_re] at hre
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (2 * q) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hsq : (2 * (q : ℂ)) ^ (1 / 2 : ℂ) = (c : ℂ) := by
    rw [hc, Complex.ofReal_cpow (by positivity)]; push_cast; ring_nf
  have hsq' : (2 * (q : ℂ)) ^ (2⁻¹ : ℂ) = (c : ℂ) := by rw [← one_div]; exact hsq
  obtain ⟨xr, hxr⟩ : ∃ xr : E 2, xr = !₂[c * Real.cos (θ 0), -(c * Real.sin (θ 0))] := ⟨_, rfl⟩
  have hW : polarW (q : ℂ) (ofRe θ 0) = ofR xr := by
    funext i; fin_cases i
    · simp [polarW, ofR, ofRe, hxr, hsq']
    · simp [polarW, ofR, ofRe, hxr, hsq']
  rw [hP, hW] at hw
  have hK := h.ham.real xr (θ 1) hw
  have hRe : R (ofR xr) (θ 1 : ℂ) = Kbnf ν b R (ofR xr) (θ 1) -
      ((ν / 2 * (xr 0 ^ 2 + xr 1 ^ 2) + b / 4 * (xr 0 ^ 2 + xr 1 ^ 2) ^ 2 : ℝ) : ℂ) := by
    simp only [Kbnf, ofR]; push_cast; ring
  show ((ω 1 : ℂ) * ((b : ℂ) * (I 0 : ℂ) ^ 2 +
    R (polarW (p0 ν b (ofRe ω) + ofRe I 0) (ofRe θ 0)) (θ 1 : ℂ))).im = 0
  rw [hP, hW, hRe]
  simp [Complex.mul_im, hK, ← Complex.ofReal_pow]

theorem polarW_add_two_pi (P θ : ℂ) : polarW P (θ + 2 * π) = polarW P θ := by
  simp only [polarW, Complex.cos_add_two_pi, Complex.sin_add_two_pi]

theorem pertP_per {ν b ρ s : ℝ} {R : C2 → ℂ → ℂ} (hH : IsTPHam (Kbnf ν b R) ρ s) (j : Fin 2)
    (x : Pt 2) : pertP ν b R (x.1, x.2.1 + twoPiE j, x.2.2) = pertP ν b R x := by
  revert j
  rw [Fin.forall_fin_two]
  constructor
  · have e0 : (x.2.1 + twoPiE 0 : Fin 2 → ℂ) 0 = x.2.1 0 + 2 * π := by simp [twoPiE]
    have e1 : (x.2.1 + twoPiE 0 : Fin 2 → ℂ) 1 = x.2.1 1 := by simp [twoPiE]
    show x.2.2 1 * (b * x.1 0 ^ 2 +
      R (polarW (p0 ν b x.2.2 + x.1 0) ((x.2.1 + twoPiE 0 : Fin 2 → ℂ) 0))
        ((x.2.1 + twoPiE 0 : Fin 2 → ℂ) 1)) = _
    rw [e0, e1, polarW_add_two_pi]; rfl
  · have e0 : (x.2.1 + twoPiE 1 : Fin 2 → ℂ) 0 = x.2.1 0 := by simp [twoPiE]
    have e1 : (x.2.1 + twoPiE 1 : Fin 2 → ℂ) 1 = x.2.1 1 + 2 * π := by simp [twoPiE]
    show x.2.2 1 * (b * x.1 0 ^ 2 +
      R (polarW (p0 ν b x.2.2 + x.1 0) ((x.2.1 + twoPiE 1 : Fin 2 → ℂ) 0))
        ((x.2.1 + twoPiE 1 : Fin 2 → ℂ) 1)) = _
    rw [e0, e1, R_per hH]; rfl
theorem R6_main {p : E 2} {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ}
    {h₀ : OpenPartialHomeomorph (E 2) (E 2)} {P' : E 2 → E 2} (h : BNF p ν b R ρ s C h₀ P')
    (hb : b ≠ 0) (γ : ℝ) (hγ : 0 < γ) :
    ∃ ε₀ > 0, ∃ C₁ : ℝ, ∀ ε ∈ Ioo 0 ε₀,
      IsOpen (OmegaE ν b ε) ∧ IsConnected (OmegaE ν b ε) ∧
      IsRealAnalyticOn (pertP ν b R) (DomA ν b ε s) ∧
      (∀ x ∈ DomA ν b ε s, ‖pertP ν b R x‖ ≤ C₁ * ε ^ (5 / 2 : ℝ)) ∧
      C₁ * ε ^ (5 / 2 : ℝ) ≤ γ * ε ^ (9 / 8 : ℝ) * ε ^ (5 / 4 : ℝ) * s ^ ((2 : ℝ) + 1) := by
  obtain ⟨hρ, hs, hs1⟩ := h.pos
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 2 * (|b| + 7776 * |C|) := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hM := M_nonneg ν b
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : ℝ, δ₀ = min (1 / 2) (min (1 / (4 * (M ν b + 1)))
      (min (ρ / 6) (γ * s ^ 3 / (C₁ + 1)))) := ⟨_, rfl⟩
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀]
    exact lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hroot : (δ₀ ^ 8) ^ (1 / 8 : ℝ) = δ₀ := by
    rw [show (1 / 8 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast hδ₀pos.le (by norm_num)
  refine ⟨δ₀ ^ 8, by positivity, C₁, fun ε hε => ?_⟩
  obtain ⟨hε0, hε1⟩ := hε
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε ^ (1 / 8 : ℝ) := ⟨_, rfl⟩
  have hδ : 0 < δ := hδdef ▸ Real.rpow_pos_of_pos hε0 _
  have hδlt : δ < δ₀ := hδdef ▸ hroot ▸ Real.rpow_lt_rpow hε0.le hε1 (by norm_num)
  have pw : ∀ k : ℕ, ε ^ ((k : ℝ) / 8) = δ ^ k := fun k => hδdef ▸ rpow_eighths hε0.le k
  have e8 : ε = δ ^ 8 := by have := pw 8; norm_num at this; exact this
  have e9 : ε ^ (9 / 8 : ℝ) = δ ^ 9 := by have := pw 9; norm_num at this; exact this
  have e10 : ε ^ (5 / 4 : ℝ) = δ ^ 10 := by have := pw 10; norm_num at this; exact this
  have e20 : ε ^ (5 / 2 : ℝ) = δ ^ 20 := by have := pw 20; norm_num at this; exact this
  have hs3 : s ^ (3 : ℝ) = s ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hs21 : s ^ ((2 : ℝ) + 1) = s ^ 3 := by
    rw [show (2 : ℝ) + 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hδ₀] at hδlt
  have hd1 : δ < 1 / 2 := hδlt.trans_le (min_le_left _ _)
  have hd2 : δ < 1 / (4 * (M ν b + 1)) :=
    hδlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hd3 : δ < ρ / 6 :=
    hδlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hd4 : δ < γ * s ^ 3 / (C₁ + 1) :=
    hδlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδM : (M ν b + 1) * δ ≤ 1 / 4 := by
    rw [lt_div_iff₀ (by positivity)] at hd2; linarith
  have hC : C₁ * δ ≤ γ * s ^ 3 := by
    rw [lt_div_iff₀ (by positivity)] at hd4; nlinarith
  have hδ1 : δ ≤ 1 := by linarith
  have hh : ε ^ (9 / 8 : ℝ) * s ^ (3 : ℝ) ≤ δ ^ 9 := by
    rw [e9, hs3]; exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hs.le hs1)
  -- the facts used on `DomA`
  have hF : ∀ x ∈ DomA ν b ε s, x.2.2 1 ≠ 0 ∧ ‖x.2.2 1‖ ≤ 2 ∧ ‖x.1 0‖ < δ ^ 10 ∧
      0 < (p0 ν b x.2.2 + x.1 0).re ∧
      ‖polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0)‖ ≤ 6 * δ ^ 4 ∧
      ‖polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0)‖ < ρ ∧ |(x.2.1 1).im| < s := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := dom_facts hb hδ hd1.le hδM e8 e10 hh hx
    have hW : ‖polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0)‖ ≤ 6 * δ ^ 4 := by
      have hP2 : ‖2 * (p0 ν b x.2.2 + x.1 0)‖ ≤ (2 * δ ^ 4) ^ 2 := by
        rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]; nlinarith
      have hexp : Real.exp |(x.2.1 0).im| ≤ 3 :=
        (Real.exp_le_exp.mpr (h6.le.trans hs1)).trans Real.exp_one_lt_three.le
      calc _ ≤ 2 * δ ^ 4 * Real.exp |(x.2.1 0).im| := norm_polarW_le (by positivity) hP2
        _ ≤ 2 * δ ^ 4 * 3 := mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = 6 * δ ^ 4 := by ring
    have hδ4 : δ ^ 4 ≤ δ := pow_le_of_le_one hδ.le hδ1 (by norm_num)
    exact ⟨h1, h2, h3, h4, hW, by linarith, h7⟩
  refine ⟨omegaE_isOpen ν b ε hb, omegaE_isConnected ν b ε hε0, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, -, -, h4, -, h6, h7⟩ := hF x hx
    exact (pertP_diffAt (R_holo h.ham) h1 h4 h6 h7).differentiableWithinAt
  · intro I θ ω hx
    obtain ⟨-, -, -, h4, -, h6, -⟩ := hF _ hx
    exact pertP_real h I θ ω h4 h6
  · intro j x _
    exact pertP_per h.ham j x
  · intro x hx
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hF x hx
    have hRb : ‖R (polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0)) (x.2.1 1)‖ ≤ |C| * (6 * δ ^ 4) ^ 5 :=
      calc _ ≤ C * ‖polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0)‖ ^ 5 := h.rem _ h6 _ h7
        _ ≤ |C| * ‖polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0)‖ ^ 5 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * (6 * δ ^ 4) ^ 5 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h5 5) (abs_nonneg C)
    have hbI : ‖(b : ℂ) * x.1 0 ^ 2‖ ≤ |b| * δ ^ 20 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      calc |b| * ‖x.1 0‖ ^ 2 ≤ |b| * (δ ^ 10) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h3.le 2) (abs_nonneg b)
        _ = |b| * δ ^ 20 := by ring
    show ‖x.2.2 1 * ((b : ℂ) * x.1 0 ^ 2 +
      R (polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0)) (x.2.1 1))‖ ≤ _
    rw [e20, norm_mul]
    calc _ ≤ 2 * (|b| * δ ^ 20 + |C| * (6 * δ ^ 4) ^ 5) :=
          mul_le_mul h2 ((norm_add_le _ _).trans (add_le_add hbI hRb)) (norm_nonneg _)
            (by norm_num)
      _ = C₁ * δ ^ 20 := by rw [hC₁]; ring
  · rw [e20, e9, e10, hs21]
    calc C₁ * δ ^ 20 = δ ^ 19 * (C₁ * δ) := by ring
      _ ≤ δ ^ 19 * (γ * s ^ 3) := mul_le_mul_of_nonneg_left hC (by positivity)
      _ = γ * δ ^ 9 * δ ^ 10 * s ^ 3 := by ring

end ABC.S4.R6Aux
