import ABC.S4.TwistConjAux1

/-! T1 helpers: a `C³` map `ℂ → ℂ` (over `ℝ`) has a 3-jet in `w, w̄` (Peano remainder). -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

set_option linter.unusedSimpArgs false

noncomputable section

namespace ABC.S4.TwistConjAux

open ABC

/-- the jet of a ray primitive: `d/dt c(tw) = α(tw) Re w + β(tw) Im w` -/
def integ (c0 : ℂ) (α β : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, 0 => c0
  | 1, 0 => (α 0 0 - Complex.I * β 0 0) / 2
  | 0, 1 => (α 0 0 + Complex.I * β 0 0) / 2
  | 2, 0 => (α 1 0 - Complex.I * β 1 0) / 4
  | 1, 1 => (α 0 1 + α 1 0 - Complex.I * β 0 1 + Complex.I * β 1 0) / 4
  | 0, 2 => (α 0 1 + Complex.I * β 0 1) / 4
  | 3, 0 => (α 2 0 - Complex.I * β 2 0) / 6
  | 2, 1 => (α 1 1 + α 2 0 - Complex.I * β 1 1 + Complex.I * β 2 0) / 6
  | 1, 2 => (α 0 2 + α 1 1 - Complex.I * β 0 2 + Complex.I * β 1 1) / 6
  | 0, 3 => (α 0 2 + Complex.I * β 0 2) / 6
  | _, _ => 0

/-- drop the cubic terms -/
def trunc2 (α : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ
  | 3, 0 => 0
  | 2, 1 => 0
  | 1, 2 => 0
  | 0, 3 => 0
  | j, k => α j k

theorem ray_identity (c0 : ℂ) (α β : ℕ → ℕ → ℂ) (w : ℂ) (t : ℝ) :
    let c := integ c0 α β
    (c 1 0 * w + c 0 1 * conj w) + (c 2 0 * w ^ 2 + c 1 1 * w * conj w + c 0 2 * conj w ^ 2)
        * (2 * (t : ℂ))
      + (c 3 0 * w ^ 3 + c 2 1 * w ^ 2 * conj w + c 1 2 * w * conj w ^ 2 + c 0 3 * conj w ^ 3)
        * (3 * (t : ℂ) ^ 2) =
      jetPoly (trunc2 α) ((t : ℂ) * w) * w.re + jetPoly (trunc2 β) ((t : ℂ) * w) * w.im := by
  intro c
  rw [Complex.re_eq_add_conj, Complex.im_eq_sub_conj, jetPoly_eq, jetPoly_eq]
  simp only [c, integ, trunc2, map_mul, Complex.conj_ofReal]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring


theorem clm_decomp (L : ℂ →L[ℝ] ℂ) (w : ℂ) : L w = w.re * L 1 + w.im * L Complex.I := by
  have : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [this]
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

theorem cubic_BO (γ : ℕ → ℕ → ℂ) : BO 3 (fun w => jetPoly γ w - jetPoly (trunc2 γ) w) := by
  refine ((((BO_mono_ (γ 3 0) 3 0).add (BO_mono_ (γ 2 1) 2 1)).add
    (BO_mono_ (γ 1 2) 1 2)).add (BO_mono_ (γ 0 3) 0 3)).congr fun w => ?_
  rw [jetPoly_eq, jetPoly_eq]; simp only [trunc2]; ring

theorem jet_step {m : ℕ} (hm : m ≤ 2) {φ : ℂ → ℂ} {α β : ℕ → ℕ → ℂ}
    (hd : ∀ᶠ w in 𝓝 (0 : ℂ), DifferentiableAt ℝ φ w)
    (hx : (fun w => fderiv ℝ φ w 1 - jetPoly α w) =o[𝓝 0] fun w => ‖w‖ ^ m)
    (hy : (fun w => fderiv ℝ φ w Complex.I - jetPoly β w) =o[𝓝 0] fun w => ‖w‖ ^ m) :
    (fun w => φ w - jetPoly (integ (φ 0) α β) w) =o[𝓝 0] fun w => ‖w‖ ^ (m + 1) := by
  have ex : (fun w => fderiv ℝ φ w 1 - jetPoly (trunc2 α) w) =o[𝓝 0] fun w => ‖w‖ ^ m :=
    (hx.add ((cubic_BO α).isLittleO (by omega))).congr_left fun w => by ring
  have ey : (fun w => fderiv ℝ φ w Complex.I - jetPoly (trunc2 β) w) =o[𝓝 0]
      fun w => ‖w‖ ^ m :=
    (hy.add ((cubic_BO β).isLittleO (by omega))).congr_left fun w => by ring
  rw [isLittleO_iff]
  intro ε hε
  have hε' : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hd.and ((isLittleO_iff.1 ex) hε')).and ((isLittleO_iff.1 ey) hε'))
  refine Metric.eventually_nhds_iff_ball.2 ⟨δ, hδ, fun w hw => ?_⟩
  set c := integ (φ 0) α β with hc
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * w ∈ ball (0 : ℂ) δ := fun t ht => by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    rw [mem_ball_zero_iff] at hw
    nlinarith [norm_nonneg w, ht.2]
  set ρ' : ℝ → ℂ := fun t =>
    (fderiv ℝ φ ((t : ℂ) * w) 1 - jetPoly (trunc2 α) ((t : ℂ) * w)) * w.re +
      (fderiv ℝ φ ((t : ℂ) * w) Complex.I - jetPoly (trunc2 β) ((t : ℂ) * w)) * w.im
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
      (fun t : ℝ => φ ((t : ℂ) * w) - jetPoly c ((t : ℂ) * w)) (ρ' t) (Icc 0 1) t := by
    intro t ht
    have hdt := (hball _ (hmem t ht)).1.1
    have hin : HasDerivAt (fun t : ℝ => (t : ℂ) * w) w t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).mul_const w
    have h1 := hdt.hasFDerivAt.comp_hasDerivAt t hin
    have hT : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have h2 := ((((hT.const_mul (c 1 0 * w + c 0 1 * conj w)).add
      ((hT.pow 2).const_mul (c 2 0 * w ^ 2 + c 1 1 * w * conj w + c 0 2 * conj w ^ 2))).add
      ((hT.pow 3).const_mul (c 3 0 * w ^ 3 + c 2 1 * w ^ 2 * conj w + c 1 2 * w * conj w ^ 2
        + c 0 3 * conj w ^ 3))).const_add (c 0 0))
    have h2' : HasDerivAt (fun t : ℝ => jetPoly c ((t : ℂ) * w))
        ((c 1 0 * w + c 0 1 * conj w) + (c 2 0 * w ^ 2 + c 1 1 * w * conj w + c 0 2 * conj w ^ 2)
          * (2 * (t : ℂ)) + (c 3 0 * w ^ 3 + c 2 1 * w ^ 2 * conj w + c 1 2 * w * conj w ^ 2
            + c 0 3 * conj w ^ 3) * (3 * (t : ℂ) ^ 2)) t := by
      have e : (fun t : ℝ => jetPoly c ((t : ℂ) * w)) = fun t : ℝ => c 0 0 +
          ((c 1 0 * w + c 0 1 * conj w) * (t : ℂ) +
            (c 2 0 * w ^ 2 + c 1 1 * w * conj w + c 0 2 * conj w ^ 2) * (t : ℂ) ^ 2 +
            (c 3 0 * w ^ 3 + c 2 1 * w ^ 2 * conj w + c 1 2 * w * conj w ^ 2
              + c 0 3 * conj w ^ 3) * (t : ℂ) ^ 3) := by
        funext t; rw [jetPoly_ray]; ring
      rw [e]
      convert h2 using 1
      push_cast
      ring
    refine (h1.sub h2').hasDerivWithinAt.congr_deriv ?_
    simp only [Function.comp_def, ρ']
    rw [clm_decomp (fderiv ℝ φ ((t : ℂ) * w)) w, ray_identity]
    ring
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖ρ' t‖ ≤ ε * ‖w‖ ^ (m + 1) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    obtain ⟨⟨-, b1⟩, b2⟩ := hball _ (hmem t ht')
    have hn : ‖(t : ℂ) * w‖ ≤ ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht'.1]
      nlinarith [norm_nonneg w, ht'.2]
    have hp : ‖(t : ℂ) * w‖ ^ m ≤ ‖w‖ ^ m := pow_le_pow_left₀ (norm_nonneg _) hn m
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at b1 b2
    have hre : ‖(w.re : ℂ)‖ ≤ ‖w‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_re_le_norm w
    have him : ‖(w.im : ℂ)‖ ≤ ‖w‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_im_le_norm w
    calc ‖ρ' t‖ ≤ ‖fderiv ℝ φ ((t : ℂ) * w) 1 - jetPoly (trunc2 α) ((t : ℂ) * w)‖ * ‖(w.re : ℂ)‖
          + ‖fderiv ℝ φ ((t : ℂ) * w) Complex.I - jetPoly (trunc2 β) ((t : ℂ) * w)‖
            * ‖(w.im : ℂ)‖ := by
          simp only [ρ']
          exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ε / 2 * ‖w‖ ^ m * ‖w‖ + ε / 2 * ‖w‖ ^ m * ‖w‖ := by
          gcongr
          · exact b1.trans (by gcongr)
          · exact b2.trans (by gcongr)
      _ = ε * ‖w‖ ^ (m + 1) := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    (right_mem_Icc.2 zero_le_one)
  have h0 : φ (((0 : ℝ) : ℂ) * w) - jetPoly c (((0 : ℝ) : ℂ) * w) = 0 := by
    rw [Complex.ofReal_zero, zero_mul, jetPoly_eq]; simp [c, integ]
  simp only [h0, sub_zero, Complex.ofReal_one, one_mul] at key
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa using key

/-- the constant jet -/
def const0 (a : ℂ) : ℕ → ℕ → ℂ
  | 0, 0 => a
  | _, _ => 0

/-- Taylor with Peano remainder in `w, w̄`, up to order 3 -/
theorem taylor : ∀ (n : ℕ), n ≤ 3 → ∀ {φ : ℂ → ℂ}, ContDiffAt ℝ n φ 0 →
    ∃ c : ℕ → ℕ → ℂ, (fun w => φ w - jetPoly c w) =o[𝓝 0] fun w => ‖w‖ ^ n
  | 0, _, φ, hφ => by
    refine ⟨const0 (φ 0), ?_⟩
    simp only [pow_zero]
    rw [isLittleO_one_iff]
    have : Tendsto (fun w => φ w - φ 0) (𝓝 0) (𝓝 (φ 0 - φ 0)) :=
      (hφ.continuousAt.tendsto).sub tendsto_const_nhds
    rw [sub_self] at this
    refine this.congr fun w => ?_
    rw [jetPoly_eq]; simp [const0]
  | n + 1, hn, φ, hφ => by
    have hfd : ContDiffAt ℝ n (fderiv ℝ φ) 0 := hφ.fderiv_right (by push_cast; rfl)
    obtain ⟨α, hα⟩ := taylor n (by omega) (φ := fun w => fderiv ℝ φ w 1)
      (hfd.clm_apply contDiffAt_const)
    obtain ⟨β, hβ⟩ := taylor n (by omega) (φ := fun w => fderiv ℝ φ w Complex.I)
      (hfd.clm_apply contDiffAt_const)
    have hd : ∀ᶠ w in 𝓝 (0 : ℂ), DifferentiableAt ℝ φ w :=
      (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
    exact ⟨_, jet_step (by omega) hd hα hβ⟩

end ABC.S4.TwistConjAux
