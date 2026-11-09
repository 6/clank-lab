import ABC.S4.R5
import ABC.S4.R123
import ABC.S4.R6Aux

/-! R6: Pöschel's hypotheses. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

theorem R6_hyps {p : E 2} {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ} {h₀ : OpenPartialHomeomorph (E 2) (E 2)}
    {P' : E 2 → E 2} (h : BNF p ν b R ρ s C h₀ P') (hb : b ≠ 0) (γ : ℝ) (hγ : 0 < γ) :
    ∃ ε₀ > 0, ∃ C₁ : ℝ, ∀ ε ∈ Ioo 0 ε₀,
      IsOpen (OmegaE ν b ε) ∧ IsConnected (OmegaE ν b ε) ∧
      IsRealAnalyticOn (pertP ν b R) (DomA ν b ε s) ∧
      (∀ x ∈ DomA ν b ε s, ‖pertP ν b R x‖ ≤ C₁ * ε ^ (5 / 2 : ℝ)) ∧
      C₁ * ε ^ (5 / 2 : ℝ) ≤ γ * ε ^ (9 / 8 : ℝ) * ε ^ (5 / 4 : ℝ) * s ^ ((2 : ℝ) + 1) :=
  R6Aux.R6_main h hb γ hγ

end ABC.S4
