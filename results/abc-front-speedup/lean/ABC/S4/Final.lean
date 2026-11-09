import ABC.S4.R4
import ABC.S4.R6
import ABC.S4.R7Invariant
import ABC.S4.R7Measure
import ABC.S4.FinalAux4
import ABC.S4.FinalAux8
import ABC.S4.FinalAux9

/-! (K″) from the certificate and Theorem A. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

set_option maxHeartbeats 1000000 in
theorem HAND_KAM_curves_proof (p : E 2) (hp : CertFacts p) (δ : ℝ) (hδ : 0 < δ) :
    KAMCurves p δ := by
  obtain ⟨ν, b, R, ρB, s, C, h₀, P', hB⟩ := R123 hp
  have hb := R4_b_ne_zero hp hB
  have hbpos : 0 < |b| := abs_pos.2 hb
  obtain ⟨hρB, hs, hs1⟩ := hB.pos
  obtain ⟨γ, hγ, c, hc, hThA⟩ := Poschel2001.theorem_A 2 le_rfl 2 (by norm_num)
  obtain ⟨ε₀, hε₀, C₁, hR6⟩ := R6_hyps hB hb γ hγ
  obtain ⟨ρK, L₁, hρK, hρKlt, hL₁, hsub, hbil, himg⟩ :=
    FinalAux.chart_bilip hB.chart hρB hδ
  set C₁' := max C₁ 0 with hC₁'
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  set S := s ^ ((2 : ℝ) + 1) with hSdef
  have hS0 : 0 < S := Real.rpow_pos_of_pos hs _
  have hS1 : S ≤ 1 := Real.rpow_le_one hs.le hs1 (by norm_num)
  have hS3 : s ^ (3 : ℝ) = S := by rw [hSdef]; norm_num
  set a₁ := c * C₁' / S with ha₁
  set a₃ := c * C₁' / (2 * |b|) with ha₃
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₃0 : 0 ≤ a₃ := by positivity
  obtain ⟨e, he0, he1, heε, hea₁, hea₂, hea₃, heρB, heρK, hemeas⟩ :=
    FinalAux.small_e (a₁ := a₁) (a₂ := 24 * |b| * a₁ / S) (a₃ := a₃) (N := 2 + |ν|)
      hε₀ hρB hρK hbpos
  set ε := e ^ 8 with hεdef
  have hε0 : 0 < ε := by positivity
  obtain ⟨hΩo, hΩc, hana, hbound, hineq⟩ := hR6 ε ⟨hε0, heε⟩
  have hr_eq : ε ^ (5 / 4 : ℝ) = e ^ 10 := FinalAux.pow8_rpow he0.le _ 10 (by norm_num)
  have hα_eq : ε ^ (9 / 8 : ℝ) = e ^ 9 := FinalAux.pow8_rpow he0.le _ 9 (by norm_num)
  have hη_eq : ε ^ (5 / 2 : ℝ) = e ^ 20 := FinalAux.pow8_rpow he0.le _ 20 (by norm_num)
  set r := ε ^ (5 / 4 : ℝ) with hrdef
  set α := ε ^ (9 / 8 : ℝ) with hαdef
  set η := C₁' * ε ^ (5 / 2 : ℝ) with hηdef
  have hη' : η = C₁' * e ^ 20 := by simp only [hηdef, hη_eq]
  have he2 : e ^ 2 < 1 / 2 := by nlinarith [sq_nonneg e, mul_nonneg ha₃0 (sq_nonneg e)]
  have hr0 : 0 < r := by rw [hr_eq]; positivity
  have hα0 : 0 < α := by rw [hα_eq]; positivity
  have hη0 : 0 ≤ η := by rw [hηdef, hη_eq]; positivity
  have hr1 : r ≤ 1 := by rw [hr_eq]; exact pow_le_one₀ he0.le he1.le
  have hα1 : α ≤ 1 := by rw [hα_eq]; exact pow_le_one₀ he0.le he1.le
  have hh0 : 0 < α * s ^ (3 : ℝ) := by rw [hS3]; positivity
  have hh1 : α * s ^ (3 : ℝ) ≤ 1 := by
    rw [hS3]; calc α * S ≤ 1 * 1 := mul_le_mul hα1 hS1 hS0.le zero_le_one
      _ = 1 := by ring
  -- Theorem A
  have hP : ∀ x ∈ DO r s (OmegaAlpha 2 (OmegaE ν b ε) α) (α * s ^ (3 : ℝ)),
      ‖pertP ν b R x‖ ≤ η := fun x hx =>
    (hbound x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hηle : η ≤ γ * α * r * s ^ ((2 : ℝ) + 1) := by
    rcases le_total 0 C₁ with h | h
    · have : C₁' = C₁ := max_eq_left h
      rw [hηdef, this]; exact hineq
    · have : C₁' = 0 := max_eq_right h
      rw [hηdef, this, zero_mul]; positivity
  have hαh : α * s ^ ((2 : ℝ) + 1) ≤ α * s ^ (3 : ℝ) := by rw [hS3]
  obtain ⟨φ, Φ, hA⟩ := hThA (OmegaE ν b ε) α r s (α * s ^ (3 : ℝ)) η (eNP ν b) (pertP ν b R)
    hΩo hΩc hα0 hr0 hs hh0 hr1 hs1 hh1 hana hP hηle hαh
  -- the invariant curves of `P′`
  have hrε : r ≤ ε / 2 := by
    rw [hr_eq, hεdef]
    have : e ^ 10 = e ^ 8 * e ^ 2 := by ring
    rw [this]; nlinarith [pow_pos he0 8]
  have hρ : 2 * (ε + r) ≤ ρB ^ 2 := by rw [hr_eq]; exact heρB.le
  have hD_eq : c / (α * r * s ^ ((2 : ℝ) + 1)) * η = a₁ * e := by
    rw [hα_eq, hr_eq, hη', ← hSdef, ha₁]; field_simp
  have hΛ_eq : 24 * |b| * r * ((α * s ^ ((2 : ℝ) + 1))⁻¹ * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η))
      = 24 * |b| * a₁ / S * e ^ 2 := by
    rw [hD_eq, hα_eq, hr_eq, ← hSdef]; field_simp
  have hDφ_eq : c / r * η = a₃ * (2 * |b|) * e ^ 10 := by
    rw [hr_eq, hη', ha₃]; field_simp
  have hΛφ_eq : (α * s ^ ((2 : ℝ) + 1))⁻¹ * (c / r * η) = a₁ * e := by
    rw [hDφ_eq, hα_eq, ← hSdef, ha₁, ha₃]; field_simp
  have hlo_eq : ε / 2 - c / r * η / (2 * |b|) - r = e ^ 8 * (1 / 2 - (a₃ * e ^ 2 + e ^ 2)) := by
    rw [hDφ_eq, hr_eq, hεdef]; field_simp; ring
  have hhi_eq : ε + c / r * η / (2 * |b|) + r = e ^ 8 + a₃ * e ^ 10 + e ^ 10 := by
    rw [hDφ_eq, hr_eq, hεdef]; field_simp
  obtain ⟨g, L₂, hL₂, hgprops, hlab, hinv⟩ := FinalAux.curves (P' := P') hb hs hr0 hA
    (fun ω hω => R7_time_row hα0 hA ω hω)
    (fun σ hσ u hu => R7_invariant hB hb hα0 hrε hρ hA σ hσ u hu)
    (by rw [hD_eq]; positivity) (by rw [hD_eq]; linarith)
    (by rw [hD_eq]; positivity) (by rw [hΛ_eq]; exact hea₂.le)
    (by rw [hΛφ_eq]; linarith) (by rw [hDφ_eq]; positivity)
    (by rw [hlo_eq]; have := pow_pos he0 8; nlinarith)
  -- the label set
  set K := {σ : ℝ | ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α} with hK
  have hKc : IsCompact K := FinalAux.K_isCompact hα0 hΩo
  have hKv : 0 < MeasureTheory.volume K := by
    refine lt_of_lt_of_le ?_ (R7_measure ν b ε α hb hε0 hα0 hα1)
    rw [ENNReal.ofReal_pos, hα_eq, hεdef]
    have h8 := pow_pos he0 8
    have : |b| * e ^ 8 * (1 - 8 * e ^ 9) - 16 * e ^ 9 * (2 + |ν|) =
        e ^ 8 * (|b| - (8 * |b| * e ^ 9 + 16 * e * (2 + |ν|))) := by ring
    rw [this]; exact mul_pos h8 (by linarith)
  have hglo : 0 < √(2 * (ε / 2 - c / r * η / (2 * |b|) - r)) := by
    rw [Real.sqrt_pos, hlo_eq]; have := pow_pos he0 8; nlinarith
  have hgρ : √(2 * (ε + c / r * η / (2 * |b|) + r)) < ρK := by
    rw [hhi_eq, Real.sqrt_lt' hρK]; linarith
  refine ⟨h₀, ρK, max L₁ L₂, K, g, hρK, lt_max_of_lt_left hL₁, hsub, hB.chart.1, ?_, himg,
    hKc, hKv, ?_, ?_, ?_⟩
  · intro u hu v hv
    obtain ⟨h1, h2⟩ := hbil u hu v hv
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg),
      h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)⟩
  · intro σ hσ
    obtain ⟨hc1, hc2, hc3⟩ := hgprops σ hσ
    exact ⟨hc1, hc2, fun ψ => ⟨lt_of_lt_of_le hglo (hc3 ψ).1, lt_of_le_of_lt (hc3 ψ).2 hgρ⟩⟩
  · intro σ hσ σ' hσ' ψ ψ'
    exact (hlab σ hσ σ' hσ' ψ ψ').trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)
  · intro σ hσ
    have hin : ∀ x ∈ curve g σ, ‖x‖ < ρB := by
      rintro x ⟨ψ, rfl⟩
      have h3 := (hgprops σ hσ).2.2 ψ
      rw [FinalAux.norm_polarPt, abs_of_pos (lt_of_lt_of_le hglo h3.1)]
      exact lt_of_le_of_lt h3.2 (hgρ.trans hρKlt)
    have hcongr : (fun x => retMap (h₀ x)) '' curve g σ = (fun x => h₀ (P' x)) '' curve g σ :=
      Set.image_congr (fun x hx => hB.conjP x (hin x hx))
    rw [Set.image_image, hcongr, ← Set.image_image h₀ P' (curve g σ), hinv σ hσ]

end ABC.S4
