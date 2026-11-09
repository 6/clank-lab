import ABC.S4.FlowComplex
import ABC.S4.PeriodMapAux5

/-! The period map is smooth and area-preserving. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

-- Liouville for period maps
theorem period_map_smooth {H : C2 → ℂ → ℂ} {ρ s r : ℝ} {P : E 2 → E 2} (hρ : 0 < ρ) (hs : 0 < s)
    (hH : IsTPHam H ρ s)
    (h0 : ∀ t, hamVF (H · t) 0 = 0) (hP : IsPeriodMap H P r) (hr : 0 < r) :
    ContDiffAt ℝ ⊤ P 0 ∧ jdet P 0 = 1 :=
  -- holomorphic time-`2π` map of `(w, τ) ↦ (J∇H(·, τ)(w), 1)` (`flow_complex_time`), analytic by
  -- Cauchy along complex lines; uniqueness identifies `P` with its real trace; Liouville in `ℂ³`
  PeriodMapAux.period_map_main hρ hs hH h0 hP hr

end ABC.S4
