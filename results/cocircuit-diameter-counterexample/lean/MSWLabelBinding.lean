import MSWIntegralChart
import SecondLabelEquivalence

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- The actual MSW ordered product, all81star signs and every injective
    ordered label. All original chart/regularity/bound premises are supplied
    by checked constructions. This precedes rebase/real/common-face assembly. -/
theorem mswSecond_active_label_equivalence
    (c : Option (Fin 80)) (f : Fin 41 → Fin 80) (hf : Function.Injective f) :
    let P := secondIntegralMatrix mswIntegralA mswIntegralStarChart
    let B := starEnvelope P integerVandermonde
      (secondIntegralChart mswIntegralA mswIntegralStarChart mswIntegralChart_pivot)
    let N := specializedMatrix P integerVandermonde (commonParameter 41 B)
    (∃ v : Fin 41 → ℤ, (∃ j, v j ≠ 0) ∧
      (∀ i, 0 ≤ (starUnit c i : ℤ) * ∑ j, P i j * v j) ∧
      (∀ j : Fin 40, ∑ k, P (f j.succ) k * v k = 0)) ↔
    (∃ v : Fin 41 → ℚ, v ≠ 0 ∧
      (∀ i, 0 ≤ (starUnit c i : ℤ) * (N i ⬝ᵥ v)) ∧
      (∀ j : Fin 40, N (f j.succ) ⬝ᵥ v = 0)) :=
  second_active_label_equivalence mswIntegralA mswIntegralStarChart
    mswIntegralChart_pivot (by decide) c f hf

#print axioms mswSecond_active_label_equivalence
end
end ADKZPricing
