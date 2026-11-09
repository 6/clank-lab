import ABC.S4.Defs
import ABC.S4.R7MeasureAux

/-! R7: the measure of the label set. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

theorem R7_measure (ν b ε α : ℝ) (hb : b ≠ 0) (hε : 0 < ε) (hα : 0 < α) (hα1 : α ≤ 1) :
    ENNReal.ofReal (|b| * ε * (1 - 8 * α) - 16 * α * (2 + |ν|)) ≤
      MeasureTheory.volume {σ : ℝ | ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α} :=
  R7MeasureAux.measure_bound ν b ε α hb hε hα hα1

end ABC.S4
