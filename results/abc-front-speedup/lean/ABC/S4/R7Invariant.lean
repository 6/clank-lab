import ABC.S4.R7TimeRow
import ABC.S4.R123
import ABC.S4.R7InvariantAux

/-! R7: invariant curves of the period map. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

theorem R7_invariant {p : E 2} {ν b ρ s C ε α r h δ c : ℝ} {R : C2 → ℂ → ℂ}
    {h₀ : OpenPartialHomeomorph (E 2) (E 2)} {P' : E 2 → E 2} (hB : BNF p ν b R ρ s C h₀ P')
    (hb : b ≠ 0) (hα : 0 < α) (hr : r ≤ ε / 2) (hρ : 2 * (ε + r) ≤ ρ ^ 2)
    {φ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {Φ : C2 → (Fin 2 → ℝ) → Ph 2}
    (hA : Conclusion 2 c (OmegaE ν b ε) α r s h δ (eNP ν b) (pertP ν b R) φ Φ)
    (σ : ℝ) (hσ : ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α) (u : ℝ)
    (hu : ∀ θ : Fin 2 → ℝ, (Φ (ofRe θ) ![σ, 1]).2 1 = θ 1 + u) :
    let γs : ℝ → C2 := fun θ₀ =>
      polarW (p0 ν b (ofRe (φ ![σ, 1])) + (Φ (ofRe ![θ₀, -u]) ![σ, 1]).1 0)
        ((Φ (ofRe ![θ₀, -u]) ![σ, 1]).2 0)
    ∀ θ₀, ∃ x : E 2, ofR x = γs θ₀ ∧ ofR (P' x) = γs (θ₀ + 2 * π * σ) := by
  intro γs θ₀
  exact R7InvariantAux.main hB hb hα hr hρ hA σ hσ u hu θ₀

end ABC.S4
