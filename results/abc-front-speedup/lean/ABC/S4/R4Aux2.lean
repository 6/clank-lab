import ABC.S4.R4Aux1

/-! R4 helper: the period map of `Kbnf` is the rotation `g0` up to `O(‖x‖⁴)` (bootstrap +
Gronwall). -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

noncomputable section

namespace ABC.S4.R4Aux

theorem norm_vf_sub_le {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ} (hρ : 0 < ρ) (hs : 0 < s)
    (hK : IsTPHam (Kbnf ν b R) ρ s) (hR : Bound R ρ s C 5) {r : ℝ} (hrρ : r < ρ / 2) (t : ℝ)
    {w : C2} (hw : ‖w‖ < r) :
    ‖hamVF (fun w => Kbnf ν b R w t) w - F0 ν b w‖ ≤ 32 * C * r ^ 4 := by
  have hC := Bound.nonneg hρ hs hR
  have ht : (t : ℂ) ∈ strip s := by simp [strip, hs]
  have hwρ : w ∈ polydisc ρ := by simp only [polydisc, mem_ofPred_eq]; linarith
  rw [hamVF_Kbnf (differentiableAt_R hK ht hwρ), add_sub_cancel_left]
  refine (norm_JgradR_le _).trans ((norm_fderiv_R_le hρ hs hK hR ht (by linarith)).trans ?_)
  gcongr

theorem period_est_r {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ} {P' : E 2 → E 2} (hρ : 0 < ρ) (hs : 0 < s)
    (hK : IsTPHam (Kbnf ν b R) ρ s) (hR : Bound R ρ s C 5) (hP : IsPeriodMap (Kbnf ν b R) P' ρ)
    {x : E 2} {r : ℝ} (hr : 2 * ‖x‖ < r) (hr1 : r ≤ 1) (hrρ : r < ρ / 2)
    (hrG : 64 * C * Gc ν b * r ^ 3 < 1) :
    ‖ofR (P' x) - g0 ν b x (2 * π)‖ ≤ 32 * C * r ^ 4 * Gc ν b := by
  have hC := Bound.nonneg hρ hs hR
  have hG := Gc_nonneg ν b
  have hx0 := norm_nonneg x
  obtain ⟨γ, hsol, hγ0, hγ2⟩ := hP x (by linarith)
  have step : ∀ T ∈ Icc 0 (2 * π), (∀ t ∈ Ico 0 T, ‖γ t‖ < r) →
      ‖γ T - g0 ν b x T‖ ≤ 32 * C * r ^ 4 * Gc ν b := fun T hT h =>
    gron_step hr1 (by positivity) hT.1 hT.2
      (fun t ht => (hsol t ⟨ht.1, ht.2.trans hT.2⟩).mono (Icc_subset_Icc_right hT.2))
      (fun t ht => norm_vf_sub_le hρ hs hK hR hrρ t (h t ht)) (fun t ht => (h t ht).le)
      (by linarith) hγ0
  have hsmall : 32 * C * r ^ 4 * Gc ν b < r / 2 := by
    have hr0 : 0 < r := by linarith
    nlinarith [mul_lt_mul_of_pos_right hrG (by linarith : (0 : ℝ) < r / 2)]
  have hcont : ContinuousOn γ (Icc 0 (2 * π)) := fun t ht => (hsol t ht).continuousWithinAt
  have hall : ∀ t ∈ Icc 0 (2 * π), ‖γ t‖ < r := by
    by_contra hne
    push Not at hne
    set S := Icc 0 (2 * π) ∩ γ ⁻¹' {w | r ≤ ‖w‖}
    have hS : IsClosed S :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_le continuous_const continuous_norm)
    obtain ⟨t₁, ht₁, ht₁r⟩ := hne
    have hbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
    have hts := hS.csInf_mem ⟨t₁, ht₁, ht₁r⟩ hbdd
    have hlt : ∀ t ∈ Ico 0 (sInf S), ‖γ t‖ < r := fun t ht => by
      by_contra h'
      push Not at h'
      exact notMem_of_lt_csInf ht.2 hbdd ⟨⟨ht.1, ht.2.le.trans hts.1.2⟩, h'⟩
    have h1 := step _ hts.1 hlt
    have h2 := norm_g0_le ν b x (sInf S)
    have h3 := norm_le_norm_add_norm_sub' (γ (sInf S)) (g0 ν b x (sInf S))
    have h4 : r ≤ ‖γ (sInf S)‖ := hts.2
    linarith
  rw [← hγ2]
  exact step _ ⟨by positivity, le_rfl⟩ fun t ht => hall t (Ico_subset_Icc_self ht)

theorem period_est {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ} {P' : E 2 → E 2} (hρ : 0 < ρ) (hs : 0 < s)
    (hK : IsTPHam (Kbnf ν b R) ρ s) (hR : Bound R ρ s C 5) (hP : IsPeriodMap (Kbnf ν b R) P' ρ) :
    ∃ δ > 0, ∃ M, ∀ x : E 2, ‖x‖ < δ → ‖ofR (P' x) - g0 ν b x (2 * π)‖ ≤ M * ‖x‖ ^ 4 := by
  have hC := Bound.nonneg hρ hs hR
  have hG := Gc_nonneg ν b
  set r₁ := min (min (ρ / 4) 1) (1 / (64 * C * Gc ν b + 1))
  have hr₁ : 0 < r₁ := by positivity
  have hr₁a : r₁ ≤ ρ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hr₁b : r₁ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hr₁c : r₁ ≤ 1 / (64 * C * Gc ν b + 1) := min_le_right _ _
  have hgood : ∀ r, 0 ≤ r → r ≤ r₁ → 64 * C * Gc ν b * r ^ 3 < 1 := by
    intro r hr0 hr
    have h3 : r ^ 3 ≤ r := by
      have : r ≤ 1 := hr.trans hr₁b
      nlinarith [pow_le_one₀ (n := 2) hr0 this, sq_nonneg r]
    have hA : 0 ≤ 64 * C * Gc ν b := by positivity
    have : (64 * C * Gc ν b) * r ≤ (64 * C * Gc ν b) * (1 / (64 * C * Gc ν b + 1)) :=
      mul_le_mul_of_nonneg_left (hr.trans hr₁c) hA
    have : (64 * C * Gc ν b) * (1 / (64 * C * Gc ν b + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]; linarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hA]
  refine ⟨r₁ / 3, by positivity, 32 * C * 81 * Gc ν b, fun x hx => ?_⟩
  have hx0 := norm_nonneg x
  rcases eq_or_lt_of_le hx0 with h0 | hpos
  · -- `x = 0`: let `r → 0`
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ‖ofR (P' x) - g0 ν b x (2 * π)‖ ≤ 32 * C * r ^ 4 * Gc ν b := by
      have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < r₁ := nhdsWithin_le_nhds (gt_mem_nhds hr₁)
      filter_upwards [h1, self_mem_nhdsWithin] with r hr hr0
      have hr0' : (0 : ℝ) < r := hr0
      exact period_est_r hρ hs hK hR hP (by rw [← h0]; linarith) (by linarith) (by linarith)
        (hgood r hr0'.le hr.le)
    have ht : Tendsto (fun r : ℝ => 32 * C * r ^ 4 * Gc ν b) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun r : ℝ => 32 * C * r ^ 4 * Gc ν b) (𝓝 0)
          (𝓝 (32 * C * 0 ^ 4 * Gc ν b)) :=
        ((continuous_const.mul (continuous_pow 4)).mul continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have := ge_of_tendsto ht hev
    rw [← h0]
    simpa using this
  · have := period_est_r hρ hs hK hR hP (r := 3 * ‖x‖) (by linarith) (by linarith)
      (by linarith) (hgood _ (by positivity) (by linarith))
    calc _ ≤ _ := this
      _ = 32 * C * 81 * Gc ν b * ‖x‖ ^ 4 := by ring

end ABC.S4.R4Aux
