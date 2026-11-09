import ABC.S4.FinalAux3
import ABC.S4.FinalAux5
import ABC.S4.FinalAux7

/-! Final, part 3: the invariant curves of `P′` in radial-graph form, with Lipschitz label. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn Tstar W Phi0
  LipSemiLe twoPiE imPart)

noncomputable section

namespace ABC.S4.FinalAux

/-- Coefficient bookkeeping for the label bound. -/
lemma coeff_bound {b r s D Λ Λφ : ℝ} (hb : 0 < |b|) (hs : 0 < s) (hD0 : 0 ≤ D) (hD : 8 * D ≤ 1)
    (hΛ0 : 0 ≤ Λ) (hΛ : 24 * |b| * r * Λ ≤ 1) (hr : 0 < r) (hΛφ : Λφ ≤ 1 / 4) :
    1 / (4 * |b|) ≤ (1 - Λφ) / (2 * |b|) -
      (r * Λ + 4 * (r * D) / s * (s * Λ) + 4 * (r * D) / s * (2 * (s * Λ + 4 * D * (s * Λ)))) := by
  have e1 : 4 * (r * D) / s * (s * Λ) = 4 * r * D * Λ := by field_simp
  have e2 : 4 * (r * D) / s * (2 * (s * Λ + 4 * D * (s * Λ))) = 8 * r * D * Λ * (1 + 4 * D) := by
    field_simp; ring
  rw [e1, e2]
  have hrΛ : 0 ≤ r * Λ := mul_nonneg hr.le hΛ0
  have h1 : 4 * r * D * Λ ≤ r * Λ / 2 := by nlinarith
  have h2 : 8 * r * D * Λ * (1 + 4 * D) ≤ 3 / 2 * (r * Λ) := by
    have : 8 * D * (1 + 4 * D) ≤ 3 / 2 := by nlinarith
    nlinarith
  have h3 : 3 * (r * Λ) ≤ 1 / (8 * |b|) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have h4 : 3 / (8 * |b|) ≤ (1 - Λφ) / (2 * |b|) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h5 : 1 / (4 * |b|) = 3 / (8 * |b|) - 1 / (8 * |b|) := by field_simp; ring
  linarith

lemma label_core {x y F Q Ac b r s D Λ Λφ : ℝ} (hx : 0 ≤ x)
    (hcoef : 1 / (4 * |b|) ≤ (1 - Λφ) / (2 * |b|) -
      (r * Λ + 4 * (r * D) / s * (s * Λ) + 4 * (r * D) / s * (2 * (s * Λ + 4 * D * (s * Λ)))))
    (hφd : (1 - Λφ) * x / (2 * |b|) ≤ F)
    (hAct : Ac ≤ r * Λ * x + 4 * (r * D) / s * (s * Λ * x) +
      4 * (r * D) / s * (2 * y + 2 * ((s * Λ + 4 * D * (s * Λ)) * x)))
    (h1 : F - Ac ≤ Q) : x / (4 * |b|) ≤ Q + 8 * (r * D) / s * y := by
  have h2 := mul_le_mul_of_nonneg_right hcoef hx
  have e1 : (1 - Λφ) * x / (2 * |b|) = (1 - Λφ) / (2 * |b|) * x := by ring
  have e3 : x / (4 * |b|) = 1 / (4 * |b|) * x := by ring
  have e4 : r * Λ * x + 4 * (r * D) / s * (s * Λ * x) +
      4 * (r * D) / s * (2 * y + 2 * ((s * Λ + 4 * D * (s * Λ)) * x)) =
      (r * Λ + 4 * (r * D) / s * (s * Λ) + 4 * (r * D) / s * (2 * (s * Λ + 4 * D * (s * Λ)))) * x
        + 8 * (r * D) / s * y := by ring
  rw [e4] at hAct
  rw [e1] at hφd
  rw [e3]
  have e5 : ((1 - Λφ) / (2 * |b|) -
      (r * Λ + 4 * (r * D) / s * (s * Λ) + 4 * (r * D) / s * (2 * (s * Λ + 4 * D * (s * Λ))))) * x
      = (1 - Λφ) / (2 * |b|) * x -
      (r * Λ + 4 * (r * D) / s * (s * Λ) + 4 * (r * D) / s * (2 * (s * Λ + 4 * D * (s * Λ)))) * x := by
    ring
  rw [e5] at h2
  linarith

theorem curves {ν b ε c α r s h η : ℝ} {e : (Fin 2 → ℂ) → ℂ} {P : Pt 2 → ℂ}
    {φ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {Φ : C2 → (Fin 2 → ℝ) → Ph 2} {P' : E 2 → E 2}
    (hb : b ≠ 0) (hs : 0 < s) (hr : 0 < r)
    (hA : Conclusion 2 c (OmegaE ν b ε) α r s h η e P φ Φ)
    (htime : ∀ ω ∈ OmegaAlpha 2 (OmegaE ν b ε) α, φ ω 1 = ω 1 ∧
      ∃ u : ℝ, ∀ θ : Fin 2 → ℝ, (Φ (ofRe θ) ω).2 1 = θ 1 + u)
    (hinv : ∀ σ : ℝ, ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α → ∀ u : ℝ,
      (∀ θ : Fin 2 → ℝ, (Φ (ofRe θ) ![σ, 1]).2 1 = θ 1 + u) →
      ∀ θ₀, ∃ x : E 2,
        ofR x = polarW (p0 ν b (ofRe (φ ![σ, 1])) + (Φ (ofRe ![θ₀, -u]) ![σ, 1]).1 0)
          ((Φ (ofRe ![θ₀, -u]) ![σ, 1]).2 0) ∧
        ofR (P' x) = polarW (p0 ν b (ofRe (φ ![σ, 1])) +
            (Φ (ofRe ![θ₀ + 2 * π * σ, -u]) ![σ, 1]).1 0)
          ((Φ (ofRe ![θ₀ + 2 * π * σ, -u]) ![σ, 1]).2 0))
    (hD0 : 0 ≤ c / (α * r * s ^ ((2 : ℝ) + 1)) * η)
    (hD : 8 * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η) ≤ 1)
    (hΛ0 : 0 ≤ (α * s ^ ((2 : ℝ) + 1))⁻¹ * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η))
    (hΛ : 24 * |b| * r * ((α * s ^ ((2 : ℝ) + 1))⁻¹ * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η)) ≤ 1)
    (hΛφ : (α * s ^ ((2 : ℝ) + 1))⁻¹ * (c / r * η) ≤ 1 / 4)
    (hDφ0 : 0 ≤ c / r * η) (hlo : 0 < ε / 2 - c / r * η / (2 * |b|) - r) :
    ∃ (g : ℝ → ℝ → ℝ) (L : ℝ), 0 < L ∧
      (∀ σ ∈ {σ : ℝ | ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α},
        Continuous (fun ψ => g ψ σ) ∧ (∀ ψ, g (ψ + 2 * π) σ = g ψ σ) ∧
        ∀ ψ, √(2 * (ε / 2 - c / r * η / (2 * |b|) - r)) ≤ g ψ σ ∧
          g ψ σ ≤ √(2 * (ε + c / r * η / (2 * |b|) + r))) ∧
      (∀ σ ∈ {σ : ℝ | ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α},
        ∀ σ' ∈ {σ : ℝ | ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α}, ∀ ψ ψ' : ℝ,
        |σ - σ'| ≤ L * dist (polarPt (g ψ σ) ψ) (polarPt (g ψ' σ') ψ')) ∧
      ∀ σ ∈ {σ : ℝ | ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α},
        P' '' curve g σ = curve g σ := by
  set D := c / (α * r * s ^ ((2 : ℝ) + 1)) * η with hDdef
  set Λ := (α * s ^ ((2 : ℝ) + 1))⁻¹ * D with hΛdef
  set Dφ := c / r * η with hDφdef
  set Λφ := (α * s ^ ((2 : ℝ) + 1))⁻¹ * Dφ with hΛφdef
  set K := {σ : ℝ | ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α} with hK
  set Plo := ε / 2 - Dφ / (2 * |b|) - r with hPlo
  set Phi := ε + Dφ / (2 * |b|) + r with hPhi
  have hbpos : 0 < |b| := abs_pos.2 hb
  have hD0' : 0 ≤ D := hD0
  have hΛ0' : 0 ≤ Λ := hΛ0
  have hPlo0 : 0 < Plo := hlo
  have hU0 : ∀ σ ∈ K, ∃ u : ℝ, ∀ θ : Fin 2 → ℝ, (Φ (ofRe θ) ![σ, 1]).2 1 = θ 1 + u :=
    fun σ hσ => (htime _ hσ).2
  choose! U hU using hU0
  have hcirc : ∀ σ ∈ K, Function.Surjective (Ang Φ σ (U σ)) ∧
      ∀ a b, |a - b| ≤ 2 * |Ang Φ σ (U σ) a - Ang Φ σ (U σ) b| := by
    intro σ hσ
    have hl : ∀ a b, |(Ang Φ σ (U σ) a - a) - (Ang Φ σ (U σ) b - b)| ≤ (4 * D) * |a - b| :=
      fun a b => Ang_lip hA hr hs hσ (U σ) a b
    have hc : Continuous (Ang Φ σ (U σ)) := by
      have : Continuous (fun t => (Ang Φ σ (U σ) t - t)) := cont_of_lip hl
      have h2 := this.add continuous_id
      convert h2 using 1; funext t; simp
    exact circle_inv hc (by linarith) hl
  have hsurj : ∀ σ ∈ K, ∀ y, ∃ t, Ang Φ σ (U σ) t = y := fun σ hσ y => (hcirc σ hσ).1 y
  choose! T hT using hsurj
  have hinj : ∀ σ ∈ K, ∀ a b, Ang Φ σ (U σ) a = Ang Φ σ (U σ) b → a = b := by
    intro σ hσ a b hab
    have := (hcirc σ hσ).2 a b
    rw [hab, sub_self, abs_zero, mul_zero] at this
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  have hTA : ∀ σ ∈ K, ∀ t, T σ (Ang Φ σ (U σ) t) = t :=
    fun σ hσ t => hinj σ hσ _ _ (hT σ hσ _)
  have hTlip : ∀ σ ∈ K, ∀ y y', |T σ y - T σ y'| ≤ 2 * |y - y'| := by
    intro σ hσ y y'
    have := (hcirc σ hσ).2 (T σ y) (T σ y')
    rwa [hT σ hσ, hT σ hσ] at this
  have hAper : ∀ σ ∈ K, Function.Periodic (fun t => Ang Φ σ (U σ) t - t) (2 * π) := by
    intro σ hσ t
    simp only
    rw [Ang_per hA hσ]; ring
  have hActper : ∀ σ ∈ K, Function.Periodic (Act Φ σ (U σ)) (2 * π) :=
    fun σ hσ t => Act_per hA hσ _ t
  have hTper : ∀ σ ∈ K, ∀ (k : ℤ) y, T σ (y + k * (2 * π)) = T σ y + k * (2 * π) := by
    intro σ hσ k y
    apply hinj σ hσ
    rw [hT σ hσ]
    have := (hAper σ hσ).int_mul k (T σ y)
    simp only [hT σ hσ] at this
    linarith
  set Pf : ℝ → ℝ → ℝ := fun σ t => (φ ![σ, 1] 0 - ν) / (2 * b) + Act Φ σ (U σ) t with hPf
  set g : ℝ → ℝ → ℝ := fun ψ σ => √(2 * Pf σ (T σ (-ψ))) with hg
  have hPfb : ∀ σ ∈ K, ∀ t, Plo ≤ Pf σ t ∧ Pf σ t ≤ Phi := by
    intro σ hσ t
    have h1 := K_mem hb hσ
    have h2 : |φ ![σ, 1] 0 - σ| ≤ Dφ := phi_abs hA hσ
    have h3 := abs_lt.1 (Act_abs hA hσ (U σ) t)
    have h4 : |(φ ![σ, 1] 0 - ν) / (2 * b) - (σ - ν) / (2 * b)| ≤ Dφ / (2 * |b|) := by
      rw [← sub_div, abs_div, abs_mul, abs_two,
        show φ ![σ, 1] 0 - ν - (σ - ν) = φ ![σ, 1] 0 - σ by ring]
      exact div_le_div_of_nonneg_right h2 (by positivity)
    have h4' := abs_le.1 h4
    simp only [hPf, hPlo, hPhi]
    constructor <;> linarith [h1.1, h1.2, h3.1, h3.2, h4'.1, h4'.2]
  have hgcont : ∀ σ ∈ K, Continuous (fun ψ => g ψ σ) := by
    intro σ hσ
    have hTc : Continuous (T σ) := cont_of_lip (hTlip σ hσ)
    have hAc : Continuous (Act Φ σ (U σ)) := cont_of_lip (Act_lip hA hr hs hσ (U σ))
    simp only [hg, hPf]
    fun_prop
  have hgper : ∀ σ ∈ K, Function.Periodic (fun ψ => g ψ σ) (2 * π) := by
    intro σ hσ ψ
    simp only [hg, hPf]
    have := hTper σ hσ (-1) (-ψ)
    rw [show -(ψ + 2 * π) = -ψ + ((-1 : ℤ) : ℝ) * (2 * π) by push_cast; ring, this]
    have h2 := (hActper σ hσ).int_mul (-1) (T σ (-ψ))
    rw [h2]
  have hgb : ∀ σ ∈ K, ∀ ψ, √(2 * Plo) ≤ g ψ σ ∧ g ψ σ ≤ √(2 * Phi) := fun σ hσ ψ =>
    ⟨Real.sqrt_le_sqrt (by linarith [(hPfb σ hσ (T σ (-ψ))).1]),
      Real.sqrt_le_sqrt (by linarith [(hPfb σ hσ (T σ (-ψ))).2])⟩
  set Glo := √(2 * Plo) with hGlo
  set Ghi := √(2 * Phi) with hGhi
  have hGlo0 : 0 < Glo := Real.sqrt_pos.2 (by linarith)
  have hDφ0' : 0 ≤ Dφ := hDφ0
  have hGhi0 : 0 < Ghi := Real.sqrt_pos.2 (by
    have : 0 ≤ Dφ / (2 * |b|) := by positivity
    simp only [hPhi]; linarith)
  set L := 4 * |b| * (Ghi + 4 * π * (r * D) / (s * Glo)) with hLdef
  have hL : 0 < L := by positivity
  refine ⟨g, L, hL, fun σ hσ => ⟨hgcont σ hσ, hgper σ hσ, hgb σ hσ⟩, ?_, ?_⟩
  · intro σ hσ σ' hσ' ψ ψ'
    obtain ⟨k, hk⟩ := exists_int_abs_sub_le ψ ψ'
    set ψ'' := ψ' + 2 * π * k with hψ''
    have hgk : g ψ'' σ' = g ψ' σ' := by
      have := (hgper σ' hσ').int_mul k ψ'
      rw [show ψ'' = ψ' + k * (2 * π) by rw [hψ'']; ring]
      exact this
    have hpt : polarPt (g ψ' σ') ψ' = polarPt (g ψ'' σ') ψ'' := by
      rw [hgk, hψ'', polarPt_add_int]
    rw [hpt]
    set a := T σ (-ψ) with ha
    set a' := T σ' (-ψ'') with ha'
    set x := |σ - σ'| with hx
    set y := |ψ - ψ''| with hy
    have hx0 : 0 ≤ x := abs_nonneg _
    have hy0 : 0 ≤ y := abs_nonneg _
    have hAa : Ang Φ σ (U σ) a = -ψ := hT σ hσ _
    have hAa' : Ang Φ σ' (U σ') a' = -ψ'' := hT σ' hσ' _
    have hUl : |U σ - U σ'| ≤ s * Λ * x := u_lip hA hr hs hσ hσ' (hU σ hσ) (hU σ' hσ')
    -- the angle at `a'` for the two labels
    have hE1 : |Ang Φ σ (U σ) a' - Ang Φ σ' (U σ') a'| ≤ (s * Λ + 4 * D * (s * Λ)) * x := by
      have h1 : |Ang Φ σ (U σ) a' - Ang Φ σ' (U σ) a'| ≤ s * Λ * x := Ang_σ hA hr hs hσ hσ' _ _
      have h2 : |Ang Φ σ' (U σ) a' - Ang Φ σ' (U σ') a'| ≤ 4 * D * |U σ - U σ'| :=
        Ang_u hA hr hs hσ' _ _ _
      have h3 : 4 * D * |U σ - U σ'| ≤ 4 * D * (s * Λ * x) :=
        mul_le_mul_of_nonneg_left hUl (by positivity)
      calc _ ≤ |Ang Φ σ (U σ) a' - Ang Φ σ' (U σ) a'| +
            |Ang Φ σ' (U σ) a' - Ang Φ σ' (U σ') a'| := abs_sub_le _ _ _
        _ ≤ s * Λ * x + 4 * D * (s * Λ * x) := add_le_add h1 (h2.trans h3)
        _ = _ := by ring
    have haa : |a - a'| ≤ 2 * y + 2 * ((s * Λ + 4 * D * (s * Λ)) * x) := by
      have h1 := (hcirc σ hσ).2 a a'
      rw [hAa] at h1
      have e : -ψ - Ang Φ σ (U σ) a' =
          -(ψ - ψ'') - (Ang Φ σ (U σ) a' - Ang Φ σ' (U σ') a') := by rw [hAa']; ring
      have h2 : |-ψ - Ang Φ σ (U σ) a'| ≤ y + (s * Λ + 4 * D * (s * Λ)) * x := by
        rw [e]
        refine (abs_sub _ _).trans ?_
        rw [abs_neg]; linarith
      linarith
    -- the action
    have hAct : |Act Φ σ (U σ) a - Act Φ σ' (U σ') a'| ≤
        r * Λ * x + 4 * (r * D) / s * (s * Λ * x) +
          4 * (r * D) / s * (2 * y + 2 * ((s * Λ + 4 * D * (s * Λ)) * x)) := by
      have h1 : |Act Φ σ (U σ) a - Act Φ σ' (U σ) a| ≤ r * Λ * x := Act_σ hA hr hs hσ hσ' _ _
      have h2 : |Act Φ σ' (U σ) a - Act Φ σ' (U σ') a| ≤ 4 * (r * D) / s * |U σ - U σ'| :=
        Act_u hA hr hs hσ' _ _ _
      have h3 : |Act Φ σ' (U σ') a - Act Φ σ' (U σ') a'| ≤ 4 * (r * D) / s * |a - a'| :=
        Act_lip hA hr hs hσ' _ _ _
      have hc0 : 0 ≤ 4 * (r * D) / s := by positivity
      have h2' := h2.trans (mul_le_mul_of_nonneg_left hUl hc0)
      have h3' := h3.trans (mul_le_mul_of_nonneg_left haa hc0)
      calc _ ≤ |Act Φ σ (U σ) a - Act Φ σ' (U σ) a| +
            |Act Φ σ' (U σ) a - Act Φ σ' (U σ') a'| := abs_sub_le _ _ _
        _ ≤ |Act Φ σ (U σ) a - Act Φ σ' (U σ) a| + (|Act Φ σ' (U σ) a - Act Φ σ' (U σ') a| +
            |Act Φ σ' (U σ') a - Act Φ σ' (U σ') a'|) := by gcongr; exact abs_sub_le _ _ _
        _ ≤ _ := by linarith
    -- the shifted frequency
    have hφd : (1 - Λφ) * x / (2 * |b|) ≤ |(φ ![σ, 1] 0 - ν) / (2 * b) - (φ ![σ', 1] 0 - ν) / (2 * b)| := by
      have h1 : |(φ ![σ, 1] 0 - σ) - (φ ![σ', 1] 0 - σ')| ≤ Λφ * x := phi_lip hA hσ hσ'
      have e : (φ ![σ, 1] 0 - ν) / (2 * b) - (φ ![σ', 1] 0 - ν) / (2 * b) =
          (φ ![σ, 1] 0 - φ ![σ', 1] 0) / (2 * b) := by ring
      rw [e, abs_div, abs_mul, abs_two]
      rw [div_le_div_iff_of_pos_right (by positivity)]
      have e2 : σ - σ' = (φ ![σ, 1] 0 - φ ![σ', 1] 0) - ((φ ![σ, 1] 0 - σ) - (φ ![σ', 1] 0 - σ')) := by
        ring
      have h3 : x ≤ |φ ![σ, 1] 0 - φ ![σ', 1] 0| + Λφ * x := by
        have := abs_sub (φ ![σ, 1] 0 - φ ![σ', 1] 0) ((φ ![σ, 1] 0 - σ) - (φ ![σ', 1] 0 - σ'))
        rw [← e2, ← hx] at this
        linarith
      linarith
    -- lower bound for the action difference
    have hcoef := coeff_bound (b := b) hbpos hs hD0' hD hΛ0' hΛ hr hΛφ
    have hPfd : x / (4 * |b|) ≤ |Pf σ a - Pf σ' a'| + 8 * (r * D) / s * y := by
      have e : Pf σ a - Pf σ' a' =
          ((φ ![σ, 1] 0 - ν) / (2 * b) - (φ ![σ', 1] 0 - ν) / (2 * b)) +
            (Act Φ σ (U σ) a - Act Φ σ' (U σ') a') := by simp only [hPf]; ring
      have h1 : |(φ ![σ, 1] 0 - ν) / (2 * b) - (φ ![σ', 1] 0 - ν) / (2 * b)| -
          |Act Φ σ (U σ) a - Act Φ σ' (U σ') a'| ≤ |Pf σ a - Pf σ' a'| := by
        rw [e]
        have := abs_sub_abs_le_abs_sub ((φ ![σ, 1] 0 - ν) / (2 * b) - (φ ![σ', 1] 0 - ν) / (2 * b))
          (-(Act Φ σ (U σ) a - Act Φ σ' (U σ') a'))
        rwa [abs_neg, sub_neg_eq_add] at this
      exact label_core hx0 hcoef hφd hAct h1
    -- from the action difference to the distance
    have hg1 : g ψ σ = √(2 * Pf σ a) := rfl
    have hg2 : g ψ'' σ' = √(2 * Pf σ' a') := rfl
    have hPa := hPfb σ hσ a
    have hPa' := hPfb σ' hσ' a'
    have hsq1 : Pf σ a = g ψ σ ^ 2 / 2 := by
      rw [hg1, Real.sq_sqrt (by linarith)]; ring
    have hsq2 : Pf σ' a' = g ψ'' σ' ^ 2 / 2 := by
      rw [hg2, Real.sq_sqrt (by linarith)]; ring
    have hb1 := hgb σ hσ ψ
    have hb2 := hgb σ' hσ' ψ''
    set dd := dist (polarPt (g ψ σ) ψ) (polarPt (g ψ'' σ') ψ'') with hdd
    have hrad : |g ψ σ - g ψ'' σ'| ≤ dd :=
      abs_sub_le_dist_polarPt _ _ _ _ (by linarith) (by linarith)
    have hang : min (g ψ σ) (g ψ'' σ') * (2 / π) * y ≤ dd :=
      angle_le_dist_polarPt (by linarith) (by linarith) hk
    have hPd : |Pf σ a - Pf σ' a'| ≤ Ghi * dd := by
      rw [hsq1, hsq2]
      have e : g ψ σ ^ 2 / 2 - g ψ'' σ' ^ 2 / 2 =
          (g ψ σ - g ψ'' σ') * ((g ψ σ + g ψ'' σ') / 2) := by ring
      rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ (g ψ σ + g ψ'' σ') / 2)]
      have : (g ψ σ + g ψ'' σ') / 2 ≤ Ghi := by linarith
      calc _ ≤ dd * ((g ψ σ + g ψ'' σ') / 2) :=
            mul_le_mul_of_nonneg_right hrad (by linarith)
        _ ≤ dd * Ghi := mul_le_mul_of_nonneg_left this (dist_nonneg)
        _ = _ := by ring
    have hyd : y ≤ π / (2 * Glo) * dd := by
      have hm : Glo ≤ min (g ψ σ) (g ψ'' σ') := le_min hb1.1 hb2.1
      have h1 : Glo * (2 / π) * y ≤ dd :=
        le_trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hm (by positivity)) hy0) hang
      calc y = π / (2 * Glo) * (Glo * (2 / π) * y) := by field_simp
        _ ≤ π / (2 * Glo) * dd := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hfin : x / (4 * |b|) ≤ (Ghi + 4 * π * (r * D) / (s * Glo)) * dd := by
      have h1 := mul_le_mul_of_nonneg_left hyd (by positivity : 0 ≤ 8 * (r * D) / s)
      have e : 8 * (r * D) / s * (π / (2 * Glo) * dd) = 4 * π * (r * D) / (s * Glo) * dd := by
        field_simp; ring
      rw [e] at h1
      rw [add_mul]
      linarith
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * |b|)).1 hfin
    calc x ≤ _ := this
      _ = L * dd := by rw [hLdef]; ring
  · intro σ hσ
    set X : ℝ → E 2 := fun t => polarPt (√(2 * Pf σ t)) (-Ang Φ σ (U σ) t) with hXdef
    have hcurve : curve g σ = range X := by
      ext y; simp only [curve, mem_range]; constructor
      · rintro ⟨ψ, rfl⟩
        refine ⟨T σ (-ψ), ?_⟩
        simp only [hXdef, hT σ hσ, neg_neg]
        rfl
      · rintro ⟨t, rfl⟩
        refine ⟨-Ang Φ σ (U σ) t, ?_⟩
        simp only [hXdef, hg, neg_neg, hTA σ hσ]
    have hφ1 : φ ![σ, 1] 1 = 1 := by simpa using (htime _ hσ).1
    have hconv : ∀ t', polarW (p0 ν b (ofRe (φ ![σ, 1])) + (Φ (ofRe ![t', -U σ]) ![σ, 1]).1 0)
        ((Φ (ofRe ![t', -U σ]) ![σ, 1]).2 0) = ofR (X t') := by
      intro t'
      have hp0 : p0 ν b (ofRe (φ ![σ, 1])) = (((φ ![σ, 1] 0 - ν) / (2 * b) : ℝ) : ℂ) := by
        simp [p0, ofRe, hφ1]
      obtain ⟨h1, h2, -⟩ := realI hA hσ ![t', -U σ] 0
      rw [hp0, h1, h2, ← Complex.ofReal_add, polarW_ofReal]
      · rfl
      · have := (hPfb σ hσ t').1
        simp only [hPf] at this
        exact le_of_lt (lt_of_lt_of_le hPlo0 (by simpa [Act] using this))
    have hX : ∀ t, P' (X t) = X (t + 2 * π * σ) := by
      intro t
      obtain ⟨x, hx1, hx2⟩ := hinv σ hσ (U σ) (hU σ hσ) t
      rw [hconv] at hx1 hx2
      have := ofR_injective hx1
      rw [this] at hx2
      exact ofR_injective hx2
    rw [hcurve]
    ext y; constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t + 2 * π * σ, (hX t).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨X (t - 2 * π * σ), ⟨_, rfl⟩, ?_⟩
      rw [hX]; congr 1; ring

end ABC.S4.FinalAux
