import StrictChartBasis

namespace ADKZPricing
open Matrix Finset
noncomputable section

variable {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℤ)
    (C : IntegralStarChart A) (h0 : 0 < C.chart 0)

def firstProduct : Matrix (Fin (n + n)) (Fin (d + d + 1)) ℚ :=
  orderedProduct (chartedGenericFactor A C) (chartedGenericFactor A C)

include h0 in
theorem firstProduct_strict_chart :
    ∀ c v, StarFeasible (firstProduct A C) c v → v ≠ 0 → 0 < v 0 := by
  intro c v hv hn
  have hp := (chartedGenericFactor_properties A C h0).2
  exact (orderedProduct_star_strict_chart _ _ hp hp c v hv hn).1

include h0 in
theorem firstProduct_weights_exist (c : Option (Fin (n + n))) :
    ∃ w : Fin (n + n) → ℚ, (∀ i, 0 < w i) ∧
      ∀ j, (if j = 0 then 1 else 0 : ℚ) =
        ∑ i, w i * starSign c i * firstProduct A C i j := by
  exact product_star_weights _ _ (chartedGenericFactor_weights A C h0)
    (chartedGenericFactor_weights A C h0) c

def firstProductWeights (c : Option (Fin (n + n))) : Fin (n + n) → ℚ :=
  (firstProduct_weights_exist A C h0 c).choose

theorem firstProductWeights_positive (c : Option (Fin (n + n))) (i : Fin (n + n)) :
    0 < firstProductWeights A C h0 c i :=
  (firstProduct_weights_exist A C h0 c).choose_spec.1 i

theorem firstProductWeights_representation (c : Option (Fin (n + n)))
    (j : Fin (d + d + 1)) :
    (if j = 0 then 1 else 0 : ℚ) =
      ∑ i, firstProductWeights A C h0 c i * starSign c i * firstProduct A C i j :=
  (firstProduct_weights_exist A C h0 c).choose_spec.2 j

include h0 in
theorem firstProduct_basis_exists :
    ∃ f : Fin (d + d + 1) → Fin (n + n), Function.Injective f ∧
      ((firstProduct A C).submatrix f id).det ≠ 0 :=
  exists_full_row_basis _ (strict_chart_mulVec_injective _ (firstProduct_strict_chart A C h0 none))

def secondIntegralMatrix : Matrix (Fin (n + n)) (Fin (d + d + 1)) ℤ :=
  integralMatrix (firstProduct A C)

/-- Both normalizations and every chart weight have been supplied. This
    certificate has no remaining regularity, common-chart, or rank premise
    beyond the original factor's finite integral chart and positive pivot. -/
def secondIntegralChart : IntegralStarChart (secondIntegralMatrix A C) :=
  normalizedIntegralStarChart (firstProduct A C) (firstProductWeights A C h0)
    (firstProductWeights_positive A C h0) (firstProductWeights_representation A C h0)
    (firstProduct_basis_exists A C h0).choose
    (firstProduct_basis_exists A C h0).choose_spec.1
    (firstProduct_basis_exists A C h0).choose_spec.2

theorem secondIntegralChart_pivot : 0 < (secondIntegralChart A C h0).chart 0 := by
  change 0 < (if (0 : Fin (d + d + 1)) = 0 then
    (integralChartScale (firstProduct A C) (firstProductWeights A C h0) : ℤ) else 0)
  rw [if_pos rfl]
  exact_mod_cast commonDenominator_positive
    (adjustedWeights (firstProduct A C) (firstProductWeights A C h0))

def secondPerturbedMatrix : Matrix (Fin (n + n)) (Fin (d + d + 1)) ℚ :=
  chartedGenericFactor (secondIntegralMatrix A C) (secondIntegralChart A C h0)

theorem secondPerturbedMatrix_properties :
    (∀ f : Fin (d + d + 1) → Fin (n + n), Function.Injective f →
      ((secondPerturbedMatrix A C h0).submatrix f id).det ≠ 0) ∧
    (∀ c v, StarFeasible (secondPerturbedMatrix A C h0) c v → v ≠ 0 → 0 < v 0) :=
  chartedGenericFactor_properties _ _ (secondIntegralChart_pivot A C h0)

#print axioms secondIntegralChart
#print axioms secondPerturbedMatrix_properties
end
end ADKZPricing
