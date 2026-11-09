import ABC.S4.R3AuxMain

/-! R3: time-periodic Birkhoff normal form to order 4. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

-- R3
theorem R3_bnf {H₂ : C2 → ℂ → ℂ} {ρ s ν C : ℝ} (hρ : 0 < ρ) (hs : 0 < s) (hH : IsTPHam H₂ ρ s)
    (hq : Bound (fun w t => H₂ w t - ν / 2 * (w 0 ^ 2 + w 1 ^ 2)) ρ s C 3) (hnr : NonRes4 ν) :
    ∃ (ρ' s' C' b : ℝ) (R : C2 → ℂ → ℂ) (Ψ : ℂ → C2 → C2), 0 < ρ' ∧ 0 < s' ∧
      IsTPHam (Kbnf ν b R) ρ' s' ∧ Bound R ρ' s' C' 5 ∧
      DifferentiableOn ℂ (fun q : ℂ × C2 => Ψ q.1 q.2) (strip s' ×ˢ polydisc ρ') ∧
      (∀ x : E 2, ‖ofR x‖ < ρ' → ∀ i, (Ψ 0 (ofR x) i).im = 0) ∧
      (∀ t w, Ψ (t + 2 * π) w = Ψ t w) ∧ (∀ t, Ψ t 0 = 0) ∧
      (∀ t, fderiv ℂ (Ψ t) 0 = ContinuousLinearMap.id ℂ C2) ∧
      ∀ γ (t₀ t₁ : ℝ), Solves (Kbnf ν b R) γ t₀ t₁ → (∀ t ∈ Icc t₀ t₁, γ t ∈ polydisc ρ') →
        Solves H₂ (fun t => Ψ t (γ t)) t₀ t₁ :=
  R3Aux.R3_main hρ hs hH hq hnr

end ABC.S4
