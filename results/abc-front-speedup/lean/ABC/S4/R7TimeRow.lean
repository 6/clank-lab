import ABC.S4.Defs
import ABC.S4.R7TimeRowAux

/-! R7: the time component. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

-- R7
theorem R7_time_row {ν b ε α r s h δ c : ℝ} {R : C2 → ℂ → ℂ} {φ : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    {Φ : C2 → (Fin 2 → ℝ) → Ph 2}
    (hα : 0 < α) (hA : Conclusion 2 c (OmegaE ν b ε) α r s h δ (eNP ν b) (pertP ν b R) φ Φ) :
    ∀ ω ∈ OmegaAlpha 2 (OmegaE ν b ε) α, φ ω 1 = ω 1 ∧
      ∃ u : ℝ, ∀ θ : Fin 2 → ℝ, (Φ (ofRe θ) ω).2 1 = θ 1 + u :=
  R7TimeRowAux.time_row hα hA

end ABC.S4
