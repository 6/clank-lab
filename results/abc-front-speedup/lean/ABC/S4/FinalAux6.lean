import ABC.S4.Defs
import ABC.S4.FinalAux1
import ABC.S4.FinalAux2

/-! Final, part 1: componentwise consequences of Theorem A's estimates on real slices. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn Tstar W Phi0
  LipSemiLe twoPiE imPart)

noncomputable section

namespace ABC.S4.FinalAux

lemma ofRe_vec2 (a b : ℝ) : (ofRe ![a, b] : Fin 2 → ℂ) = ![(a : ℂ), (b : ℂ)] := by
  funext i; fin_cases i <;> rfl

lemma vec2_mem_Tstar {s : ℝ} (hs : 0 < s) {z w : ℂ} (hz : |z.im| < s / 2)
    (hw : |w.im| < s / 2) : (![z, w] : Fin 2 → ℂ) ∈ Tstar s := by
  show ‖imPart ![z, w]‖ < s / 2
  rw [pi_norm_lt_iff (by linarith)]
  intro i; fin_cases i
  · simpa [imPart] using hz
  · simpa [imPart] using hw

lemma ofRe_mem_Tstar {s : ℝ} (hs : 0 < s) (θ : Fin 2 → ℝ) : ofRe θ ∈ Tstar s := by
  show ‖imPart (ofRe θ)‖ < s / 2
  have : imPart (ofRe θ) = 0 := by funext i; simp [imPart, ofRe]
  rw [this, norm_zero]; linarith

lemma dist_vec2 (σ σ' : ℝ) : dist (![σ, 1] : Fin 2 → ℝ) ![σ', 1] = |σ - σ'| := by
  apply le_antisymm
  · rw [dist_pi_le_iff (abs_nonneg _)]
    intro i; fin_cases i
    · simp [Real.dist_eq]
    · simp
  · have := dist_le_pi_dist (![σ, 1] : Fin 2 → ℝ) ![σ', 1] 0
    simpa [Real.dist_eq] using this

lemma W_comp {r s K : ℝ} (hr : 0 < r) (hs : 0 < s) {x : Ph 2} (h : ‖W r s x‖ ≤ K)
    (j : Fin 2) : ‖x.1 j‖ ≤ r * K ∧ ‖x.2 j‖ ≤ s * K := by
  have h1 : ‖r⁻¹ • x.1‖ ≤ K := by have := norm_fst_le (W r s x); exact this.trans h
  have h2 : ‖s⁻¹ • x.2‖ ≤ K := by have := norm_snd_le (W r s x); exact this.trans h
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr] at h1
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs] at h2
  have h1' : ‖x.1‖ ≤ r * K := by
    rw [inv_mul_le_iff₀ hr] at h1; exact h1
  have h2' : ‖x.2‖ ≤ s * K := by
    rw [inv_mul_le_iff₀ hs] at h2; exact h2
  exact ⟨(norm_le_pi_norm x.1 j).trans h1', (norm_le_pi_norm x.2 j).trans h2'⟩

lemma W_sub (r s : ℝ) (x y : Ph 2) : W r s x - W r s y = W r s (x - y) := by
  simp only [W, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub, smul_sub]

section
variable {Ω : Set (Fin 2 → ℝ)} {c α r s h η : ℝ} {e : (Fin 2 → ℂ) → ℂ} {P : Pt 2 → ℂ}
  {φ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {Φ : C2 → (Fin 2 → ℝ) → Ph 2}

/-- Pointwise bounds from `est_Φ`. -/
lemma estI (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hr : 0 < r) (hs : 0 < s)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ Tstar s) {ω} (hω : ω ∈ OmegaAlpha 2 Ω α) (j : Fin 2) :
    ‖(Φ θ ω).1 j‖ ≤ r * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η) ∧
      ‖(Φ θ ω).2 j - θ j‖ ≤ s * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η) := by
  have := W_comp hr hs (hA.est_Φ θ hθ ω hω) j
  simpa [Phi0] using this

/-- Lipschitz-in-`ω` bounds from `est_Φ_lip`. -/
lemma lipI (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hr : 0 < r) (hs : 0 < s)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ Tstar s) {ω ω'} (hω : ω ∈ OmegaAlpha 2 Ω α)
    (hω' : ω' ∈ OmegaAlpha 2 Ω α) (j : Fin 2) :
    ‖(Φ θ ω).1 j - (Φ θ ω').1 j‖ ≤
        r * ((α * s ^ ((2 : ℝ) + 1))⁻¹ * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η)) * dist ω ω' ∧
      ‖(Φ θ ω).2 j - (Φ θ ω').2 j‖ ≤
        s * ((α * s ^ ((2 : ℝ) + 1))⁻¹ * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η)) * dist ω ω' := by
  have h0 := hA.est_Φ_lip θ hθ ω hω ω' hω'
  rw [dist_eq_norm, W_sub] at h0
  have := W_comp hr hs h0 j
  simp only [Phi0, Prod.fst_sub, Prod.snd_sub, sub_sub_sub_cancel_right, Pi.sub_apply] at this
  constructor
  · rw [mul_assoc]; exact this.1
  · rw [mul_assoc]; exact this.2

lemma realI (hA : Conclusion 2 c Ω α r s h η e P φ Φ) {ω} (hω : ω ∈ OmegaAlpha 2 Ω α)
    (θ : Fin 2 → ℝ) (j : Fin 2) :
    (Φ (ofRe θ) ω).1 j = (((Φ (ofRe θ) ω).1 j).re : ℂ) ∧
      (Φ (ofRe θ) ω).2 j = (((Φ (ofRe θ) ω).2 j).re : ℂ) ∧ |((Φ (ofRe θ) ω).1 j).re| < r := by
  obtain ⟨a, b, hab, ha⟩ := hA.real ω hω θ
  rw [hab]
  refine ⟨by simp [ofRe], by simp [ofRe], ?_⟩
  simp only [ofRe, Complex.ofReal_re]
  exact lt_of_le_of_lt (by simpa using norm_le_pi_norm a j) ha

/-- The first slice `z ↦ Φ(z, t₁)` is holomorphic on the strip. -/
lemma diff_slice0 (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hs : 0 < s) {ω}
    (hω : ω ∈ OmegaAlpha 2 Ω α) (t : ℝ) :
    DifferentiableOn ℂ (fun z : ℂ => Φ ![z, (t : ℂ)] ω) {z : ℂ | |z.im| < s / 2} := by
  have hl : Differentiable ℂ (fun z : ℂ => (![z, (t : ℂ)] : Fin 2 → ℂ)) := by
    rw [differentiable_pi]; intro i; fin_cases i
    · simp
    · simp
  refine (hA.analytic ω hω).comp hl.differentiableOn ?_
  intro z hz
  exact vec2_mem_Tstar hs hz (by simp; linarith)

lemma diff_slice1 (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hs : 0 < s) {ω}
    (hω : ω ∈ OmegaAlpha 2 Ω α) (t : ℝ) :
    DifferentiableOn ℂ (fun z : ℂ => Φ ![(t : ℂ), z] ω) {z : ℂ | |z.im| < s / 2} := by
  have hl : Differentiable ℂ (fun z : ℂ => (![(t : ℂ), z] : Fin 2 → ℂ)) := by
    rw [differentiable_pi]; intro i; fin_cases i
    · simp
    · simp
  refine (hA.analytic ω hω).comp hl.differentiableOn ?_
  intro z hz
  exact vec2_mem_Tstar hs (by simp; linarith) hz

lemma diff_proj1 {F : ℂ → Ph 2} {S : Set ℂ} (hF : DifferentiableOn ℂ F S) (j : Fin 2) :
    DifferentiableOn ℂ (fun z => (F z).1 j) S := by
  exact ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℂ _ _)).differentiable
    |>.comp_differentiableOn hF

lemma diff_proj2 {F : ℂ → Ph 2} {S : Set ℂ} (hF : DifferentiableOn ℂ F S) (j : Fin 2) :
    DifferentiableOn ℂ (fun z => (F z).2 j) S := by
  exact ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ _ _)).differentiable
    |>.comp_differentiableOn hF

/-- `θ₀`-Lipschitz bound for the action. -/
lemma lipθ0_act (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hr : 0 < r) (hs : 0 < s) {ω}
    (hω : ω ∈ OmegaAlpha 2 Ω α) (t a b : ℝ) :
    ‖(Φ (ofRe ![a, t]) ω).1 0 - (Φ (ofRe ![b, t]) ω).1 0‖ ≤
      4 * (r * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η)) / s * |a - b| := by
  have key := strip_lip (f := fun z : ℂ => (Φ ![z, (t : ℂ)] ω).1 0) (by linarith : 0 < s / 2)
    (diff_proj1 (diff_slice0 hA hs hω t) 0)
    (fun z hz => (estI hA hr hs (vec2_mem_Tstar hs hz (by simp; linarith)) hω 0).1) a b
  simp only [ofRe_vec2]
  convert key using 2; field_simp; ring

/-- `θ₁`-Lipschitz bound for the action. -/
lemma lipθ1_act (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hr : 0 < r) (hs : 0 < s) {ω}
    (hω : ω ∈ OmegaAlpha 2 Ω α) (t a b : ℝ) :
    ‖(Φ (ofRe ![t, a]) ω).1 0 - (Φ (ofRe ![t, b]) ω).1 0‖ ≤
      4 * (r * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η)) / s * |a - b| := by
  have key := strip_lip (f := fun z : ℂ => (Φ ![(t : ℂ), z] ω).1 0) (by linarith : 0 < s / 2)
    (diff_proj1 (diff_slice1 hA hs hω t) 0)
    (fun z hz => (estI hA hr hs (vec2_mem_Tstar hs (by simp; linarith) hz) hω 0).1) a b
  simp only [ofRe_vec2]
  convert key using 2; field_simp; ring

/-- `θ₀`-Lipschitz bound for the angle minus identity. -/
lemma lipθ0_ang (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hr : 0 < r) (hs : 0 < s) {ω}
    (hω : ω ∈ OmegaAlpha 2 Ω α) (t a b : ℝ) :
    ‖((Φ (ofRe ![a, t]) ω).2 0 - a) - ((Φ (ofRe ![b, t]) ω).2 0 - b)‖ ≤
      4 * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η) * |a - b| := by
  have key := strip_lip (f := fun z : ℂ => (Φ ![z, (t : ℂ)] ω).2 0 - z)
    (M := s * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η)) (by linarith : 0 < s / 2)
    ((diff_proj2 (diff_slice0 hA hs hω t) 0).sub differentiableOn_id)
    (fun z hz => by
      have := (estI hA hr hs (vec2_mem_Tstar (w := (t : ℂ)) hs hz (by simp; linarith)) hω 0).2
      simpa using this) a b
  simp only [ofRe_vec2]
  convert key using 2; field_simp; ring

/-- `θ₁`-Lipschitz bound for the angle. -/
lemma lipθ1_ang (hA : Conclusion 2 c Ω α r s h η e P φ Φ) (hr : 0 < r) (hs : 0 < s) {ω}
    (hω : ω ∈ OmegaAlpha 2 Ω α) (t a b : ℝ) :
    ‖(Φ (ofRe ![t, a]) ω).2 0 - (Φ (ofRe ![t, b]) ω).2 0‖ ≤
      4 * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η) * |a - b| := by
  have key := strip_lip (f := fun z : ℂ => (Φ ![(t : ℂ), z] ω).2 0 - t)
    (M := s * (c / (α * r * s ^ ((2 : ℝ) + 1)) * η)) (by linarith : 0 < s / 2)
    ((diff_proj2 (diff_slice1 hA hs hω t) 0).sub_const _)
    (fun z hz => by
      simpa using (estI hA hr hs (vec2_mem_Tstar hs (by simp; linarith) hz) hω 0).2) a b
  simp only [ofRe_vec2]
  convert key using 2
  · simp
  · field_simp; ring

end

end ABC.S4.FinalAux
