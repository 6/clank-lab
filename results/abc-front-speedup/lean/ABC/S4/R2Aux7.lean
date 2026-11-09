import ABC.S4.R2Aux6

/-! R2 helpers: `Q₀(t) = X(t) S R(-νt)` on the box and its 2π-periodic extension `Qf` to the
strip (`Qf = 1` off the strip). -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)
open scoped ContDiff NNReal

noncomputable section

namespace ABC.S4.R2Aux

open ABC ABC.S4

def Q0 (φ : ℂ → Cn 3 → Cn 3) (S : Matrix (Fin 2) (Fin 2) ℂ) (ν : ℝ) (t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Xf φ t * S * Rm (-(ν : ℂ) * t)

def kfl (t : ℂ) : ℤ := ⌊t.re / (2 * π)⌋

def red (t : ℂ) : ℂ := t - (kfl t : ℂ) * (2 * π)

def Qf (φ : ℂ → Cn 3 → Cn 3) (S : Matrix (Fin 2) (Fin 2) ℂ) (ν s₀ : ℝ) (t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  if |t.im| < s₀ then Q0 φ S ν (red t) else 1

theorem mat_real_mul {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : ∀ i j, (A i j).im = 0)
    (hB : ∀ i j, (B i j).im = 0) (i j : Fin 2) : ((A * B) i j).im = 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_im, hA, hB]

theorem red_re_eq (t : ℂ) : (red t).re = t.re - (kfl t : ℝ) * (2 * π) := by
  simp [red]

theorem red_re (t : ℂ) : (red t).re ∈ Ico 0 (2 * π) := by
  have hπ : 0 < 2 * π := by positivity
  have h1 := Int.floor_le (t.re / (2 * π))
  have h2 := Int.lt_floor_add_one (t.re / (2 * π))
  rw [le_div_iff₀ hπ] at h1
  rw [div_lt_iff₀ hπ] at h2
  rw [red_re_eq]
  simp only [kfl]
  constructor <;> nlinarith

theorem red_im (t : ℂ) : (red t).im = t.im := by
  simp [red]

theorem kfl_add (t : ℂ) : kfl (t + 2 * π) = kfl t + 1 := by
  have hπ : (2 * π) ≠ 0 := by positivity
  simp only [kfl]
  rw [← Int.floor_add_one]
  congr 1
  simp [Complex.add_re]; field_simp

theorem red_add (t : ℂ) : red (t + 2 * π) = red t := by
  simp only [red, kfl_add]; push_cast; ring

theorem red_mem {s₀ : ℝ} {t : ℂ} (ht : |t.im| < s₀) : red t ∈ Dom s₀ := by
  have h := red_re t
  have hs₀ : 0 < s₀ := lt_of_le_of_lt (abs_nonneg _) ht
  exact ⟨⟨by linarith [h.1], by linarith [h.2]⟩, by rw [red_im]; exact ht⟩

theorem red_real (t : ℝ) : red t = ((t - (kfl t : ℝ) * (2 * π) : ℝ) : ℂ) := by
  simp [red]

section Q

variable {H₁ : C2 → ℂ → ℂ} {ρ s s₀ r₀ : ℝ} {φ : ℂ → Cn 3 → Cn 3}
  {S : Matrix (Fin 2) (Fin 2) ℂ} {ν : ℝ}

theorem Bm_per (hH : IsTPHam H₁ ρ s) : Function.Periodic (Bm H₁) (2 * π) := fun t => by
  simp [Bm, Amat_per hH]

theorem FlowData.Q0_per (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) (hNF : NF (Xf φ (2 * π)) S ν) {u : ℂ}
    (hu : u ∈ Dom s₀) (hu' : u + 2 * π ∈ Dom s₀) : Q0 φ S ν (u + 2 * π) = Q0 φ S ν u := by
  simp only [Q0]
  rw [fd.X_per hH hρ h0 hu hu', Matrix.mul_assoc (Xf φ u), hNF.conjS, Matrix.mul_assoc,
    Matrix.mul_assoc, Rm_add, ← Matrix.mul_assoc]
  congr 2; ring

theorem FlowData.Q0_ode (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) {t : ℂ} (ht : t ∈ Dom s₀) (i j : Fin 2) :
    HasDerivAt (fun t => Q0 φ S ν t i j)
      ((Bm H₁ t * Q0 φ S ν t - (ν : ℂ) • (Q0 φ S ν t * Jm)) i j) t := by
  have h1 := hasDerivAt_mat_mul (A := Xf φ) (B := fun _ => S) (B' := 0)
    (fun i j => fd.X_ode hH hρ h0 ht i j) (fun i j => hasDerivAt_const t (S i j))
  have h2 := hasDerivAt_mat_mul (A := fun t => Xf φ t * S) (B := fun t => Rm (-(ν : ℂ) * t))
    (B' := (-(ν : ℂ)) • (Rm (-(ν : ℂ) * t) * Jm)) h1
    (fun i j => (hasDerivAt_Rm (ν : ℂ) t i j).congr_deriv (by rw [Matrix.smul_apply])) i j
  have e : (Bm H₁ t * Xf φ t * S + Xf φ t * 0) * Rm (-(ν : ℂ) * t) +
      Xf φ t * S * ((-(ν : ℂ)) • (Rm (-(ν : ℂ) * t) * Jm)) =
      Bm H₁ t * Q0 φ S ν t - (ν : ℂ) • (Q0 φ S ν t * Jm) := by
    ext i j
    simp only [Q0, Matrix.mul_zero, add_zero, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
    ring
  exact h2.congr_deriv (by rw [e])

theorem FlowData.Q0_det (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) (hNF : NF (Xf φ (2 * π)) S ν) {t : ℂ}
    (ht : t ∈ Dom s₀) : (Q0 φ S ν t).det = 1 := by
  simp [Q0, Matrix.det_mul, fd.X_det hH hρ h0 ht, hNF.det, det_Rm]

theorem FlowData.Q0_zero (fd : FlowData H₁ ρ s s₀ r₀ φ) : Q0 φ S ν 0 = S := by
  simp [Q0, fd.X_zero, Rm_zero]

theorem FlowData.Q0_real (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (hs : 0 < s) (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0)
    (hNF : NF (Xf φ (2 * π)) S ν) {t : ℝ} (ht : t ∈ Icc 0 (2 * π)) (i j : Fin 2) :
    (Q0 φ S ν t i j).im = 0 := by
  unfold Q0
  refine mat_real_mul (mat_real_mul (fd.X_real hH hρ hs h0 ht) hNF.real) ?_ i j
  intro i j
  have := Rm_real (-ν * t) i j
  push_cast at this; exact this

theorem FlowData.Q0_cont (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) (i j : Fin 2) :
    ContinuousOn (fun t => Q0 φ S ν t i j) (Dom s₀) := fun t ht =>
  (fd.Q0_ode hH hρ h0 ht i j).continuousAt.continuousWithinAt

/-- Near a point of the strip, `Qf` is a translate of `Q0`. -/
theorem FlowData.Qf_local (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) (hNF : NF (Xf φ (2 * π)) S ν) {t₀ : ℂ}
    (ht₀ : |t₀.im| < s₀) :
    ∀ᶠ t in 𝓝 t₀, t - (kfl t₀ : ℂ) * (2 * π) ∈ Dom s₀ ∧
      Qf φ S ν s₀ t = Q0 φ S ν (t - (kfl t₀ : ℂ) * (2 * π)) := by
  set k := kfl t₀
  have hπ : 0 < π := Real.pi_pos
  have hs1 := fd.s₀le1
  have hN : IsOpen {t : ℂ | |t.im| < s₀ ∧ t.re ∈ Ioo (k * (2 * π) - s₀) (k * (2 * π) + 2 * π + s₀)} :=
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).inter
      (isOpen_Ioo.preimage Complex.continuous_re)
  have hmem : t₀ ∈ {t : ℂ | |t.im| < s₀ ∧ t.re ∈ Ioo (k * (2 * π) - s₀) (k * (2 * π) + 2 * π + s₀)} := by
    have h := red_re t₀
    simp only [red, Complex.sub_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im] at h
    have hs₀ := fd.s₀pos
    refine ⟨ht₀, ?_, ?_⟩ <;> simp at h <;> linarith [h.1, h.2]
  filter_upwards [hN.mem_nhds hmem] with t ⟨hti, htr⟩
  have hu : t - (k : ℂ) * (2 * π) ∈ Dom s₀ := by
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp <;> [linarith [htr.1]; linarith [htr.2]; exact hti]
  refine ⟨hu, ?_⟩
  have hu' := red_mem hti
  simp only [Qf, hti, if_true]
  -- `red t = u - 2π m` with `m ∈ {-1, 0, 1}`
  set m := kfl t - k
  have hred : red t = t - (k : ℂ) * (2 * π) - (m : ℂ) * (2 * π) := by
    simp only [red, m]; push_cast; ring
  have hre := red_re t
  have hm2π : (m : ℝ) * (2 * π) = t.re - (red t).re - k * (2 * π) := by
    rw [red_re_eq]; simp only [m]; push_cast; ring
  have hmlt : (m : ℝ) * (2 * π) < 2 * π + s₀ := by rw [hm2π]; linarith [hre.1, htr.2]
  have hmgt : -(2 * π) - s₀ < (m : ℝ) * (2 * π) := by rw [hm2π]; linarith [hre.2, htr.1]
  have hm1 : m ≤ 1 := by
    by_contra h; push_neg at h
    have : (2 : ℝ) ≤ m := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith [Real.pi_gt_three]
  have hm2 : -1 ≤ m := by
    by_contra h; push_neg at h
    have : (m : ℝ) ≤ -2 := by exact_mod_cast (show m ≤ -2 by omega)
    have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith [Real.pi_gt_three]
  rw [hred]; rw [hred] at hu'
  clear_value m
  interval_cases m
  · -- `m = -1`
    have e : t - (k : ℂ) * (2 * π) - ((-1 : ℤ) : ℂ) * (2 * π) = (t - (k : ℂ) * (2 * π)) + 2 * π := by
      push_cast; ring
    rw [e]; rw [e] at hu'
    exact fd.Q0_per hH hρ h0 hNF hu hu'
  · simp
  · have e : t - (k : ℂ) * (2 * π) = (t - (k : ℂ) * (2 * π) - ((1 : ℤ) : ℂ) * (2 * π)) + 2 * π := by
      push_cast; ring
    conv_rhs => rw [e]
    exact (fd.Q0_per hH hρ h0 hNF hu' (by rw [← e]; exact hu)).symm

theorem Qf_per (t : ℂ) : Qf φ S ν s₀ (t + 2 * π) = Qf φ S ν s₀ t := by
  simp [Qf, red_add]

theorem FlowData.Qf_det (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) (hNF : NF (Xf φ (2 * π)) S ν) (t : ℂ) :
    (Qf φ S ν s₀ t).det = 1 := by
  unfold Qf
  split_ifs with h
  · exact fd.Q0_det hH hρ h0 hNF (red_mem h)
  · exact Matrix.det_one

theorem FlowData.Qf_zero (fd : FlowData H₁ ρ s s₀ r₀ φ) : Qf φ S ν s₀ 0 = S := by
  have : red 0 = 0 := by simp [red, kfl]
  simp [Qf, fd.s₀pos, this, fd.Q0_zero]

theorem FlowData.Qf_ode (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) (hNF : NF (Xf φ (2 * π)) S ν) {t₀ : ℂ}
    (ht₀ : |t₀.im| < s₀) (i j : Fin 2) :
    HasDerivAt (fun t => Qf φ S ν s₀ t i j)
      ((Bm H₁ t₀ * Qf φ S ν s₀ t₀ - (ν : ℂ) • (Qf φ S ν s₀ t₀ * Jm)) i j) t₀ := by
  have hloc := fd.Qf_local hH hρ h0 hNF ht₀
  obtain ⟨hu, hq⟩ := hloc.self_of_nhds
  have hev : (fun t => Qf φ S ν s₀ t i j) =ᶠ[𝓝 t₀]
      fun t => Q0 φ S ν (t - (kfl t₀ : ℂ) * (2 * π)) i j := by
    filter_upwards [hloc] with t ht; rw [ht.2]
  have h := (fd.Q0_ode hH hρ h0 (S := S) (ν := ν) hu i j).comp_sub_const t₀
    ((kfl t₀ : ℂ) * (2 * π))
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hq, (Bm_per hH).sub_int_mul_eq]

theorem FlowData.Qf_holo (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) (hNF : NF (Xf φ (2 * π)) S ν) (i j : Fin 2) :
    DifferentiableOn ℂ (fun t => Qf φ S ν s₀ t i j) (strip s₀) := fun t ht =>
  (fd.Qf_ode hH hρ h0 hNF ht i j).differentiableAt.differentiableWithinAt

theorem FlowData.Qf_real (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (hs : 0 < s) (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0)
    (hNF : NF (Xf φ (2 * π)) S ν) (t : ℝ) (i j : Fin 2) : (Qf φ S ν s₀ t i j).im = 0 := by
  have ht : |((t : ℂ)).im| < s₀ := by simp [fd.s₀pos]
  simp only [Qf, ht, if_true, red_real]
  have h := red_re t
  rw [red_real] at h
  simp only [Complex.ofReal_re] at h
  exact fd.Q0_real hH hρ hs h0 hNF ⟨h.1, h.2.le⟩ i j

theorem FlowData.Qf_bound (fd : FlowData H₁ ρ s s₀ r₀ φ) (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ)
    (h0 : ∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) (hNF : NF (Xf φ (2 * π)) S ν) :
    ∃ Kq, 0 ≤ Kq ∧ ∀ t : ℂ, |t.im| ≤ 3 * s₀ / 4 → ∀ i j, ‖Qf φ S ν s₀ t i j‖ ≤ Kq := by
  set Kt : Set ℂ := Icc 0 (2 * π) ×ℂ Icc (-(3 * s₀ / 4)) (3 * s₀ / 4)
  have hKc : IsCompact Kt := isCompact_Icc.reProdIm isCompact_Icc
  have hs₀ := fd.s₀pos
  have hKD : Kt ⊆ Dom s₀ := by
    intro u hu
    simp only [Kt, Complex.mem_reProdIm, mem_Icc] at hu
    refine ⟨⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩
  have hc : ContinuousOn (fun u => (fun i j => Q0 φ S ν u i j : Fin 2 → Fin 2 → ℂ)) Kt :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j =>
      (fd.Q0_cont hH hρ h0 i j).mono hKD
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun t ht i j => ?_⟩
  have ht' : |t.im| < s₀ := by linarith
  have hred : red t ∈ Kt := by
    have h := red_re t
    simp only [Kt, Complex.mem_reProdIm, mem_Icc, red_im]
    exact ⟨⟨h.1, h.2.le⟩, by linarith [(abs_le.1 ht).1], by linarith [(abs_le.1 ht).2]⟩
  simp only [Qf, ht', if_true]
  exact ((norm_le_pi_norm (fun j => Q0 φ S ν (red t) i j) j).trans
    ((norm_le_pi_norm (fun i j => Q0 φ S ν (red t) i j) i).trans (hC _ hred))).trans
    (le_max_left _ _)

end Q

end ABC.S4.R2Aux
