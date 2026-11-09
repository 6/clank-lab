import ABC.S4.R4Aux3
import ABC.S4.TwistConj
import ABC.S4.PeriodMap

/-! R4 helper: `period_map_smooth` for `Kbnf` and the conjugacy `retMap ≈ h₀ ∘ P′ ∘ h₀⁻¹`. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

noncomputable section

namespace ABC.S4.R4Aux

-- `Kbnf` off the strip replaced by `K₀`, so the vector field vanishes at `0` for every `t`
open Classical in
def Hc (ν b s : ℝ) (R : C2 → ℂ → ℂ) (w : C2) (t : ℂ) : ℂ :=
  if t ∈ strip s then Kbnf ν b R w t else Kbnf ν b (fun _ _ => 0) w t

theorem Hc_real (ν b s : ℝ) (hs : 0 < s) (R : C2 → ℂ → ℂ) (t : ℝ) :
    (fun w => Hc ν b s R w t) = fun w => Kbnf ν b R w t := by
  funext w
  simp [Hc, strip, hs]

theorem isTPHam_Hc {ν b ρ s : ℝ} {R : C2 → ℂ → ℂ} (hs : 0 < s) (hK : IsTPHam (Kbnf ν b R) ρ s) :
    IsTPHam (Hc ν b s R) ρ s where
  holo := hK.holo.congr fun q hq => by simp [Hc, hq.2]
  real x t hx := by
    have := congrFun (Hc_real ν b s hs R t) (ofR x)
    rw [this]
    exact hK.real x t hx
  per w t := by
    have hiff : t + 2 * π ∈ strip s ↔ t ∈ strip s := by simp [strip]
    by_cases ht : t ∈ strip s
    · simp only [Hc, hiff, ht, ite_true]; exact hK.per w t
    · simp only [Hc, hiff, ht, ite_false]; simp [Kbnf]

theorem Hc_vf_zero {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ} (hρ : 0 < ρ) (hs : 0 < s)
    (hK : IsTPHam (Kbnf ν b R) ρ s) (hR : Bound R ρ s C 5) (t : ℂ) :
    hamVF (Hc ν b s R · t) 0 = 0 := by
  by_cases ht : t ∈ strip s
  · have e : (Hc ν b s R · t) = fun w => Kbnf ν b R w t := by funext w; simp [Hc, ht]
    rw [e, hamVF_Kbnf (differentiableAt_R hK ht (by simp [polydisc, hρ]))]
    have h0 : fderiv ℂ (fun w => R w t) 0 = 0 := by
      have := norm_fderiv_R_le hρ hs hK hR ht (w := 0) (by simp; linarith)
      simpa using this
    rw [h0]
    ext i; fin_cases i <;> simp [F0]
  · have e : (Hc ν b s R · t) = fun w => Kbnf ν b (fun _ _ => 0) w t := by
      funext w; simp [Hc, ht]
    rw [e, hamVF_Kbnf (differentiableAt_const _)]
    ext i; fin_cases i <;> simp [F0]

theorem isPeriodMap_Hc {ν b ρ s : ℝ} {R : C2 → ℂ → ℂ} {P' : E 2 → E 2} (hs : 0 < s)
    (hP : IsPeriodMap (Kbnf ν b R) P' ρ) : IsPeriodMap (Hc ν b s R) P' ρ := by
  intro x hx
  obtain ⟨γ, hγ, h0, h1⟩ := hP x hx
  refine ⟨γ, fun t ht => ?_, h0, h1⟩
  rw [Hc_real ν b s hs R t]
  exact hγ t ht

theorem period_smooth {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ} {P' : E 2 → E 2} (hρ : 0 < ρ)
    (hs : 0 < s) (hK : IsTPHam (Kbnf ν b R) ρ s) (hR : Bound R ρ s C 5)
    (hP : IsPeriodMap (Kbnf ν b R) P' ρ) : ContDiffAt ℝ ⊤ P' 0 ∧ jdet P' 0 = 1 :=
  period_map_smooth hρ hs (isTPHam_Hc hs hK) (Hc_vf_zero hρ hs hK hR) (isPeriodMap_Hc hs hP) hρ

theorem period_zero {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ} {P' : E 2 → E 2} (hρ : 0 < ρ)
    (hs : 0 < s) (hK : IsTPHam (Kbnf ν b R) ρ s) (hR : Bound R ρ s C 5)
    (hP : IsPeriodMap (Kbnf ν b R) P' ρ) : P' 0 = 0 := by
  obtain ⟨δ, hδ, M, hM⟩ := period_est hρ hs hK hR hP
  have h := hM 0 (by simpa using hδ)
  have hg : g0 ν b 0 (2 * π) = 0 := by ext i; fin_cases i <;> simp [g0]
  rw [hg, sub_zero, norm_zero] at h
  have h' : ofR (P' 0) = 0 := norm_le_zero_iff.1 (by simpa using h)
  ext i
  have := congrFun h' i
  simpa [ofR] using this

theorem b_ne_zero_core {p : E 2} (hp : CertFacts p) {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ}
    {h₀ : OpenPartialHomeomorph (E 2) (E 2)} {P' : E 2 → E 2} (h : BNF p ν b R ρ s C h₀ P') :
    b ≠ 0 := by
  obtain ⟨hρ, hs, -⟩ := h.pos
  obtain ⟨hsm, hdetP⟩ := period_smooth hρ hs h.ham h.rem h.period
  have hP0 := period_zero hρ hs h.ham h.rem h.period
  obtain ⟨hh0, hball, hsrcopen, hsmooth, hsmooth'⟩ := h.chart
  have h0src : (0 : E 2) ∈ h₀.source := hball (mem_ball_self hρ)
  have hpt : p ∈ h₀.target := hh0 ▸ h₀.map_source h0src
  have hsp : h₀.symm p = 0 := by rw [← hh0]; exact h₀.left_inv h0src
  have hsymm : ContDiffAt ℝ ⊤ h₀.symm p := hsmooth'.contDiffAt (h₀.open_target.mem_nhds hpt)
  have hh : ContDiffAt ℝ ⊤ h₀ 0 := hsmooth.contDiffAt (hsrcopen.mem_nhds h0src)
  -- `retMap = h₀ ∘ P′ ∘ h₀⁻¹` near `p`
  have hev1 : ∀ᶠ y in 𝓝 (0 : E 2), ‖y‖ < ρ ∧ P' y ∈ ball 0 ρ := by
    filter_upwards [ball_mem_nhds (0 : E 2) hρ,
      hsm.continuousAt.preimage_mem_nhds (by rw [hP0]; exact ball_mem_nhds (0 : E 2) hρ)]
      with y hy hy'
    exact ⟨mem_ball_zero_iff.1 hy, hy'⟩
  have hev2 : ∀ᶠ x in 𝓝 p, ‖h₀.symm x‖ < ρ ∧ P' (h₀.symm x) ∈ ball 0 ρ := by
    have hc : Tendsto h₀.symm (𝓝 p) (𝓝 0) := by rw [← hsp]; exact h₀.continuousAt_symm hpt
    exact hc.eventually hev1
  have hconj : ∀ᶠ x in 𝓝 p, retMap x = h₀ (P' (h₀.symm x)) := by
    filter_upwards [hev2, h₀.open_target.mem_nhds hpt] with x hx hxt
    rw [← h.conjP _ hx.1, h₀.right_inv hxt]
  have hc : ∀ᶠ x in 𝓝 p, P' (h₀.symm x) = h₀.symm (retMap x) := by
    filter_upwards [hconj, hev2] with x hx hx2
    rw [hx, h₀.left_inv (hball hx2.2)]
  -- derivatives
  set A := fderiv ℝ h₀ 0
  set B := fderiv ℝ P' 0
  set Cs := fderiv ℝ h₀.symm p
  have hA : HasFDerivAt h₀ A (h₀.symm p) := by
    rw [hsp]; exact (hh.differentiableAt (by simp)).hasFDerivAt
  have hA' : HasFDerivAt h₀ A (P' (h₀.symm p)) := by rw [hsp, hP0]; rw [hsp] at hA; exact hA
  have hB : HasFDerivAt P' B (h₀.symm p) := by
    rw [hsp]; exact (hsm.differentiableAt (by simp)).hasFDerivAt
  have hC : HasFDerivAt h₀.symm Cs p := (hsymm.differentiableAt (by simp)).hasFDerivAt
  have hret : HasFDerivAt retMap (A.comp (B.comp Cs)) p :=
    (hA'.comp p (hB.comp p hC)).congr_of_eventuallyEq hconj
  have hid : HasFDerivAt (fun x => h₀ (h₀.symm x)) (A.comp Cs) p := hA.comp p hC
  have hid' : HasFDerivAt (fun x => h₀ (h₀.symm x)) (ContinuousLinearMap.id ℝ (E 2)) p := by
    refine (hasFDerivAt_id p).congr_of_eventuallyEq ?_
    filter_upwards [h₀.open_target.mem_nhds hpt] with x hx
    exact h₀.right_inv hx
  have hAC : A.comp Cs = ContinuousLinearMap.id ℝ (E 2) := hid.unique hid'
  have hdet : jdet retMap p = 1 := by
    have h1 : LinearMap.det (A : E 2 →ₗ[ℝ] E 2) * LinearMap.det (Cs : E 2 →ₗ[ℝ] E 2) = 1 := by
      rw [← LinearMap.det_comp, ← ContinuousLinearMap.toLinearMap_comp, hAC]
      simp
    have hB1 : LinearMap.det (B : E 2 →ₗ[ℝ] E 2) = 1 := hdetP
    rw [jdet, hret.fderiv, ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.det_comp, LinearMap.det_comp, hB1]
    linear_combination h1
  have hretC : ContDiffAt ℝ 3 retMap p := by
    have hA3 : ContDiffAt ℝ 3 h₀ (P' (h₀.symm p)) := by rw [hsp, hP0]; exact hh.of_le le_top
    have hB3 : ContDiffAt ℝ 3 P' (h₀.symm p) := by rw [hsp]; exact hsm.of_le le_top
    exact (hA3.comp p (hB3.comp p (hsymm.of_le le_top))).congr_of_eventuallyEq hconj
  have hker : (fderiv ℝ h₀.symm p).ker = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have hm' : Cs m = 0 := hm
    have : (A.comp Cs) m = m := by rw [hAC]; rfl
    rw [ContinuousLinearMap.comp_apply, hm', map_zero] at this
    rw [← this]
    exact Submodule.zero_mem _
  have htw := twist_conj (f₁ := retMap) (f₂ := P') (h := h₀.symm) (hsymm.of_le le_top) hker hretC
    hdet hc hp.twist
  rw [hsp] at htw
  intro hb0
  have hβ := twist_indep hdetP htw (twistData_period hρ hs h.ham h.rem h.nonres h.period)
  apply hβ
  rw [beta_ajet, hb0]
  simp

end ABC.S4.R4Aux
