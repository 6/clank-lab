import ABC.S4.R123
import ABC.S4.TwistPhi
import ABC.S4.R4Aux4

/-! R4: the normal-form twist `b` is nonzero. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

-- R4
theorem R4_period_twist {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ} {P' : E 2 → E 2}
    (hρ : 0 < ρ) (hs : 0 < s) (hK : IsTPHam (Kbnf ν b R) ρ s) (hR : Bound R ρ s C 5) (hnr : NonRes4 ν)
    (hP : IsPeriodMap (Kbnf ν b R) P' ρ) :
    ∃ a, TwistData P' 0 ![1 / 2, -Complex.I / 2] a ∧
      birkhoffBeta a = -2 * π * Complex.I * b * a 1 0 :=
  ⟨R4Aux.ajet ν b, R4Aux.twistData_period hρ hs hK hR hnr hP, R4Aux.beta_ajet ν b⟩

theorem R4_b_ne_zero {p : E 2} (hp : CertFacts p) {ν b ρ s C : ℝ} {R : C2 → ℂ → ℂ}
    {h₀ : OpenPartialHomeomorph (E 2) (E 2)} {P' : E 2 → E 2} (h : BNF p ν b R ρ s C h₀ P') :
    b ≠ 0 :=
  R4Aux.b_ne_zero_core hp h

end ABC.S4
