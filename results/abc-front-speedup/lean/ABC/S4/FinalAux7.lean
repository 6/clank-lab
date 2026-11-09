import ABC.S4.FinalAux6

/-! Final, part 2: the real angle and action of the invariant curves, as functions of `θ₀`. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn Tstar W Phi0
  LipSemiLe twoPiE imPart)

noncomputable section

namespace ABC.S4.FinalAux

/-- The angle `Φ^∠₀(θ₀, -u; (σ, 1))`, real part. -/
def Ang (Φ : C2 → (Fin 2 → ℝ) → Ph 2) (σ u t : ℝ) : ℝ := ((Φ (ofRe ![t, -u]) ![σ, 1]).2 0).re

/-- The action `Φ^I₀(θ₀, -u; (σ, 1))`, real part. -/
def Act (Φ : C2 → (Fin 2 → ℝ) → Ph 2) (σ u t : ℝ) : ℝ := ((Φ (ofRe ![t, -u]) ![σ, 1]).1 0).re

lemma cont_of_lip {f : ℝ → ℝ} {K : ℝ} (h : ∀ a b, |f a - f b| ≤ K * |a - b|) :
    Continuous f := by
  have : LipschitzWith (Real.toNNReal (max K 0)) f := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (le_max_right _ _)]
    exact (h a b).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  exact this.continuous

lemma ofRe_shift (t u : ℝ) :
    ofRe ![t, -u] + twoPiE 0 = (ofRe ![t + 2 * π, -u] : Fin 2 → ℂ) := by
  funext i; fin_cases i <;> simp [ofRe, twoPiE]

section
variable {Ω : Set (Fin 2 → ℝ)} {c α r s h η : ℝ} {e : (Fin 2 → ℂ) → ℂ} {P : Pt 2 → ℂ}
  {φ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {Φ : C2 → (Fin 2 → ℝ) → Ph 2}

lemma Ang_per (hA : Conclusion 2 c Ω α r s h η e P φ Φ) {σ : ℝ}
    (hσ : ![σ, 1] ∈ OmegaAlpha 2 Ω α) (u t : ℝ) :
    Ang Φ σ u (t + 2 * π) = Ang Φ σ u t + 2 * π := by
  have := hA.periodic _ hσ 0 ![t, -u]
  rw [ofRe_shift] at this
  simp only [Ang, this, Prod.snd_add, Pi.add_apply, Complex.add_re]
  simp [twoPiE]

lemma Act_per (hA : Conclusion 2 c Ω α r s h η e P φ Φ) {σ : ℝ}
    (hσ : ![σ, 1] ∈ OmegaAlpha 2 Ω α) (u t : ℝ) :
    Act Φ σ u (t + 2 * π) = Act Φ σ u t := by
  have := hA.periodic _ hσ 0 ![t, -u]
  rw [ofRe_shift] at this
  simp only [Act, this, Prod.fst_add, Pi.add_apply, Complex.add_re]
  simp

lemma Ang_lip (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hr : 0 < r) (hs : 0 < s) {σ : ℝ}
    (hσ : ![σ, 1] ∈ OmegaAlpha 2 Ω α) (u a b : ℝ) :
    |(Ang Φ σ u a - a) - (Ang Φ σ u b - b)| ≤
      4 * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η) * |a - b| := by
  refine le_trans ?_ (lipθ0_ang hA hr hs hσ (-u) a b)
  refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
  simp [Ang]

lemma Act_lip (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hr : 0 < r) (hs : 0 < s) {σ : ℝ}
    (hσ : ![σ, 1] ∈ OmegaAlpha 2 Ω α) (u a b : ℝ) :
    |Act Φ σ u a - Act Φ σ u b| ≤
      4 * (r * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η)) / s * |a - b| := by
  refine le_trans ?_ (lipθ0_act hA hr hs hσ (-u) a b)
  refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
  simp [Act]

lemma Ang_u (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hr : 0 < r) (hs : 0 < s) {σ : ℝ}
    (hσ : ![σ, 1] ∈ OmegaAlpha 2 Ω α) (u u' t : ℝ) :
    |Ang Φ σ u t - Ang Φ σ u' t| ≤ 4 * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η) * |u - u'| := by
  have := lipθ1_ang hA hr hs hσ t (-u) (-u')
  rw [show -u - -u' = -(u - u') by ring, abs_neg] at this
  refine le_trans ?_ this
  refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
  simp [Ang]

lemma Act_u (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hr : 0 < r) (hs : 0 < s) {σ : ℝ}
    (hσ : ![σ, 1] ∈ OmegaAlpha 2 Ω α) (u u' t : ℝ) :
    |Act Φ σ u t - Act Φ σ u' t| ≤
      4 * (r * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η)) / s * |u - u'| := by
  have := lipθ1_act hA hr hs hσ t (-u) (-u')
  rw [show -u - -u' = -(u - u') by ring, abs_neg] at this
  refine le_trans ?_ this
  refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
  simp [Act]

lemma Ang_σ (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hr : 0 < r) (hs : 0 < s) {σ σ' : ℝ}
    (hσ : ![σ, 1] ∈ OmegaAlpha 2 Ω α) (hσ' : ![σ', 1] ∈ OmegaAlpha 2 Ω α) (u t : ℝ) :
    |Ang Φ σ u t - Ang Φ σ' u t| ≤
      s * ((α * s ^ ((2 : ℝ) + 1))⁻¹ * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η)) * |σ - σ'| := by
  have := (lipI hA hr hs (ofRe_mem_Tstar hs ![t, -u]) hσ hσ' 0).2
  rw [dist_vec2] at this
  refine le_trans ?_ this
  refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
  simp [Ang]

lemma Act_σ (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hr : 0 < r) (hs : 0 < s) {σ σ' : ℝ}
    (hσ : ![σ, 1] ∈ OmegaAlpha 2 Ω α) (hσ' : ![σ', 1] ∈ OmegaAlpha 2 Ω α) (u t : ℝ) :
    |Act Φ σ u t - Act Φ σ' u t| ≤
      r * ((α * s ^ ((2 : ℝ) + 1))⁻¹ * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η)) * |σ - σ'| := by
  have := (lipI hA hr hs (ofRe_mem_Tstar hs ![t, -u]) hσ hσ' 0).1
  rw [dist_vec2] at this
  refine le_trans ?_ this
  refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
  simp [Act]

lemma u_lip (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hr : 0 < r) (hs : 0 < s) {σ σ' u u' : ℝ}
    (hσ : ![σ, 1] ∈ OmegaAlpha 2 Ω α) (hσ' : ![σ', 1] ∈ OmegaAlpha 2 Ω α)
    (hu : ∀ θ : Fin 2 → ℝ, (Φ (ofRe θ) ![σ, 1]).2 1 = θ 1 + u)
    (hu' : ∀ θ : Fin 2 → ℝ, (Φ (ofRe θ) ![σ', 1]).2 1 = θ 1 + u') :
    |u - u'| ≤
      s * ((α * s ^ ((2 : ℝ) + 1))⁻¹ * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η)) * |σ - σ'| := by
  have := (lipI hA hr hs (ofRe_mem_Tstar hs 0) hσ hσ' 1).2
  rw [dist_vec2, hu, hu'] at this
  refine le_trans (le_of_eq ?_) this
  rw [add_sub_add_left_eq_sub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

lemma Act_abs (hA : Conclusion 2 c Ω α r s h η e P φ Φ) {σ : ℝ}
    (hσ : ![σ, 1] ∈ OmegaAlpha 2 Ω α) (u t : ℝ) : |Act Φ σ u t| < r :=
  (realI hA hσ ![t, -u] 0).2.2

lemma phi_abs (hA : Conclusion 2 c Ω α r s h η e P φ Φ) {σ : ℝ}
    (hσ : ![σ, 1] ∈ OmegaAlpha 2 Ω α) : |φ ![σ, 1] 0 - σ| ≤ c / r * η := by
  have h1 := hA.est_φ _ hσ
  have h2 := norm_le_pi_norm (φ ![σ, 1] - ![σ, 1]) 0
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h2
  simpa using h2.trans h1

lemma phi_lip (hA : Conclusion 2 c Ω α r s h η e P φ Φ) {σ σ' : ℝ}
    (hσ : ![σ, 1] ∈ OmegaAlpha 2 Ω α) (hσ' : ![σ', 1] ∈ OmegaAlpha 2 Ω α) :
    |(φ ![σ, 1] 0 - σ) - (φ ![σ', 1] 0 - σ')| ≤
      (α * s ^ ((2 : ℝ) + 1))⁻¹ * (c / r * η) * |σ - σ'| := by
  have h1 := hA.est_φ_lip _ hσ _ hσ'
  rw [dist_vec2, dist_eq_norm] at h1
  have h2 := norm_le_pi_norm ((φ ![σ, 1] - ![σ, 1]) - (φ ![σ', 1] - ![σ', 1])) 0
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h2
  simpa using h2.trans h1

end

end ABC.S4.FinalAux
