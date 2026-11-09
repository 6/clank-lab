import ABC.S4.Defs

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

noncomputable section

namespace ABC.S4.FinalAux

theorem chart_bilip {h : OpenPartialHomeomorph (E 2) (E 2)} {p : E 2} {ρ δ : ℝ}
    (hc : IsChart h p ρ) (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ ρ' L : ℝ, 0 < ρ' ∧ ρ' < ρ ∧ 0 < L ∧ closedBall (0 : E 2) ρ' ⊆ h.source ∧
      (∀ u ∈ closedBall (0 : E 2) ρ', ∀ v ∈ closedBall (0 : E 2) ρ',
        dist (h u) (h v) ≤ L * dist u v ∧ dist u v ≤ L * dist (h u) (h v)) ∧
      h '' closedBall 0 ρ' ⊆ ball p δ := by
  obtain ⟨h0, hball, hopen, hcd, hcds⟩ := hc
  have h0s : (0 : E 2) ∈ h.source := hball (mem_ball_self hρ)
  have hpt : p ∈ h.target := h0 ▸ h.map_source h0s
  have hda : ContDiffAt ℝ ⊤ h 0 := hcd.contDiffAt (hopen.mem_nhds h0s)
  have hdb : ContDiffAt ℝ ⊤ h.symm p := hcds.contDiffAt (h.open_target.mem_nhds hpt)
  set A := fderiv ℝ h 0 with hAdef
  set B := fderiv ℝ h.symm p with hBdef
  have hA : HasStrictFDerivAt h A 0 := hda.hasStrictFDerivAt (by simp)
  have hB : HasFDerivAt h.symm B p := (hdb.differentiableAt (by simp)).hasFDerivAt
  have hBA : ∀ x, B (A x) = x := by
    have h1 : HasFDerivAt (h.symm ∘ h) (B.comp A) 0 := by
      have hB' : HasFDerivAt h.symm B (h 0) := by rw [h0]; exact hB
      exact hB'.comp (0 : E 2) hA.hasFDerivAt
    have h2 : HasFDerivAt (h.symm ∘ h) (ContinuousLinearMap.id ℝ (E 2)) 0 := by
      apply (hasFDerivAt_id (0 : E 2)).congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds h0s] with x hx
      exact h.left_inv hx
    have h3 := h1.unique h2
    intro x
    exact congrArg (fun T : E 2 →L[ℝ] E 2 => T x) h3
  set c : NNReal := (2 * (‖B‖₊ + 1))⁻¹ with hcdef
  have hcpos : 0 < c := by positivity
  obtain ⟨S, hS, hap⟩ := hA.approximates_deriv_on_nhds (c := c) (Or.inr hcpos)
  have hcR : (c : ℝ) * (‖B‖ + 1) = 1 / 2 := by
    rw [hcdef]; push_cast
    have : (0:ℝ) < ‖B‖ + 1 := by positivity
    field_simp
  have hc0 : (0 : ℝ) ≤ c := c.2
  have hcont : ContinuousAt h 0 := hda.continuousAt
  have hV : h ⁻¹' ball p δ ∈ 𝓝 (0 : E 2) :=
    hcont.preimage_mem_nhds (by rw [h0]; exact ball_mem_nhds p hδ)
  have hT : S ∩ ball 0 ρ ∩ h ⁻¹' ball p δ ∈ 𝓝 (0 : E 2) :=
    inter_mem (inter_mem hS (ball_mem_nhds 0 hρ)) hV
  obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.1 hT
  have hsub : closedBall (0 : E 2) (min (ε / 2) (ρ / 2)) ⊆ S ∩ ball 0 ρ ∩ h ⁻¹' ball p δ :=
    (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))).trans hεb
  refine ⟨min (ε / 2) (ρ / 2), max (max (‖A‖ + c) (2 * ‖B‖)) 1, by positivity,
    lt_of_le_of_lt (min_le_right _ _) (by linarith), by positivity,
    fun x hx => hball (hsub hx).1.2, ?_, ?_⟩
  · intro u hu v hv
    have key := hap u (hsub hu).1.1 v (hsub hv).1.1
    rw [dist_eq_norm, dist_eq_norm]
    set w := u - v
    have hAw : ‖A w‖ ≤ ‖A‖ * ‖w‖ := A.le_opNorm w
    have hBw : ‖w‖ ≤ ‖B‖ * ‖A w‖ := by
      calc ‖w‖ = ‖B (A w)‖ := by rw [hBA]
        _ ≤ ‖B‖ * ‖A w‖ := B.le_opNorm _
    have t1 : ‖h u - h v‖ ≤ ‖A w‖ + c * ‖w‖ := by
      have := norm_add_le (h u - h v - A w) (A w)
      simp only [sub_add_cancel] at this
      linarith
    have t2 : ‖A w‖ ≤ ‖h u - h v‖ + c * ‖w‖ := by
      have := norm_sub_le (h u - h v) (h u - h v - A w)
      simp only [sub_sub_cancel] at this
      linarith
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
    have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
    have hL1 : ‖A‖ + c ≤ max (max (‖A‖ + c) (2 * ‖B‖)) 1 :=
      (le_max_left _ _).trans (le_max_left _ _)
    have hL2 : 2 * ‖B‖ ≤ max (max (‖A‖ + c) (2 * ‖B‖)) 1 :=
      (le_max_right _ _).trans (le_max_left _ _)
    have hd0 : 0 ≤ ‖h u - h v‖ := norm_nonneg _
    constructor
    · calc ‖h u - h v‖ ≤ (‖A‖ + c) * ‖w‖ := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hL1 hw0
    · have s1 : ‖w‖ ≤ ‖B‖ * ‖h u - h v‖ + ‖B‖ * c * ‖w‖ := by nlinarith
      have s2 : ‖B‖ * c * ‖w‖ ≤ ‖w‖ / 2 := by
        have : ‖B‖ * c ≤ 1 / 2 := by nlinarith
        nlinarith
      calc ‖w‖ ≤ 2 * ‖B‖ * ‖h u - h v‖ := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hL2 hd0
  · rintro _ ⟨x, hx, rfl⟩
    exact (hsub hx).2

end ABC.S4.FinalAux
