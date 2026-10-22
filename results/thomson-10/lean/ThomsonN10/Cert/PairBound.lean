import ThomsonN10.Interfaces
import ThomsonN10.Cert.L1.Main
import ThomsonN10.Cert.L1.Data.Residual

namespace ThomsonN10.Cert
set_option exponentiation.threshold 1000
set_option maxHeartbeats 0

/-- The checked minorant uses the shared 17 coefficients, with the epsilon subtracted
from the constant coefficient and four trailing zero coefficients. -/
theorem hNew_eq_minorant (t : ℝ) : L1.hNew t = minorant t := by
  norm_num [L1.hNew, L1.hNewCoeff, minorant, hCoeff, minorantEps, Fin.sum_univ_succ]
  ring

theorem certifiedEnergy_eq : (L1.certifiedEnergyReduced : ℝ) =
    (certU : ℝ) - (certLoss : ℝ) := by
  norm_num [L1.certifiedEnergyReduced, certU, certLoss]

/-- This is the requested three-point certificate lower bound on the capped domain.
The full identity and residual L1 bound are checked by integer Kronecker arithmetic.
`L1.Data.residual_agrees_JSON` separately checks the supplied residual exactly. -/
theorem PairBound_holds : ThomsonN10.Interfaces.PairBound := by
  intro x hx hcap
  have hc : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ (13/20 : ℝ) := by
    simpa [pairCap] using hcap
  have hb := L1.reduced_pair_bound x hx.1 hc
  rw [certifiedEnergy_eq] at hb
  simpa only [hNew_eq_minorant] using hb

end ThomsonN10.Cert
#print axioms ThomsonN10.Cert.PairBound_holds
#print axioms ThomsonN10.Cert.L1.Data.residual_agrees_JSON
