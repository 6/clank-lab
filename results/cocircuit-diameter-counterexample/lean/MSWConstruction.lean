import MSWIntegralChart
import NormalizedRegularity
import KernelRayTransport
import EndpointMatrixBridge

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- This is the actual frozen source array, with only its checked positive
    row denominators cleared. Every original row label is retained. -/
theorem msw_integer_source_binding :
    mswIntegralA.map (Int.castRingHom ℚ) =
      rowScaled mswSource (fun i => (mswIntegralRowScales i : ℚ)) := by
  ext i j
  exact mswIntegral_positive_scaling i j

theorem msw_integer_source_cells (c : Option (Fin 40)) (v : Fin 21 → ℚ) :
    StarFeasible (mswIntegralA.map (Int.castRingHom ℚ)) c v ↔ StarFeasible mswSource c v := by
  rw [msw_integer_source_binding]
  exact rowScaled_star_iff _ _ (fun i => by exact_mod_cast mswIntegral_scales_positive i) c v

def mswFirstFactor : Matrix (Fin 40) (Fin 21) ℚ :=
  chartedGenericFactor mswIntegralA mswIntegralStarChart

def mswProduct : Matrix (Fin 80) (Fin 41) ℚ :=
  firstProduct mswIntegralA mswIntegralStarChart

/-- An actual rational 80-by-41 construction. The designated endpoint
    transport and distance claim are separate obligations, not fields. -/
def mswFinalMatrix : Matrix (Fin 80) (Fin 41) ℚ :=
  secondPerturbedMatrix mswIntegralA mswIntegralStarChart mswIntegralChart_pivot

theorem mswFinal_uniform : Uniform mswFinalMatrix := by
  unfold mswFinalMatrix
  exact second_uniform_endpoint mswIntegralA mswIntegralStarChart mswIntegralChart_pivot

theorem mswFinal_real_strict_chart :
    ∀ c v, StarFeasible (mswFinalMatrix.map (Rat.castHom ℝ)) c v → v ≠ 0 → 0 < v 0 :=
  (chartedGenericFactor_real_properties
    (secondIntegralMatrix mswIntegralA mswIntegralStarChart)
    (secondIntegralChart mswIntegralA mswIntegralStarChart mswIntegralChart_pivot)
    (secondIntegralChart_pivot mswIntegralA mswIntegralStarChart mswIntegralChart_pivot)).2

theorem mswProduct_real_kernel_labels
    (c : Option (Fin 80)) (v : Fin 41 → ℝ)
    (hv : StarFeasible (mswProduct.map (Rat.castHom ℝ)) c v)
    (hne : v ≠ 0) (label : Fin 40 → Fin 80) (hl : Function.Injective label)
    (ha : ∀ j, (mswProduct.map (Rat.castHom ℝ)) (label j) ⬝ᵥ v = 0) :
    let q := affineKernel (mswProduct.submatrix label id)
    v = (v 0) • (fun j => ((q j : ℚ) : ℝ)) ∧
    (∀ c', StarFeasible (mswProduct.map (Rat.castHom ℝ)) c' v ↔ StarFeasible mswProduct c' q) ∧
    (∀ i, (mswProduct.map (Rat.castHom ℝ)) i ⬝ᵥ v = 0 ↔ mswProduct i ⬝ᵥ q = 0) :=
  firstProduct_real_kernel_labels mswIntegralA mswIntegralStarChart
    mswIntegralChart_pivot (by decide) c v hv hne label hl ha

/-- All81cell regularity is supplied for the actual normalized product,
    with no abstract regularity or common-chart premise. -/
theorem mswSecond_regularOrderedLabel
    (c : Option (Fin 80)) (f : Fin 41 → Fin 80)
    (hf : Function.Injective (fun j : Fin 40 => f j.succ)) :
    RegularOrderedLabel (secondIntegralMatrix mswIntegralA mswIntegralStarChart) (starUnit c) f :=
  secondIntegral_regularity mswIntegralA mswIntegralStarChart
    mswIntegralChart_pivot (by decide) c f hf

#print axioms mswFinal_uniform
#print axioms mswFinal_real_strict_chart
#print axioms mswProduct_real_kernel_labels
#print axioms mswSecond_regularOrderedLabel
end
end ADKZPricing
