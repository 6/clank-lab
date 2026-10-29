import MSWConstruction
import SignedCellFaces

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- Geometric closed common faces for actual real MSW PRODUCT vertices.
    All spatial-minor/strict-inactive premises are discharged; remaining
    arguments are the actual vertex coordinates and their original labels. -/
theorem msw_product_common_face (c : Option (Fin 80)) (p q : Fin 41 → ℝ)
    (hp0 : p 0 = 1) (hq0 : q 0 = 1)
    (hp : StarFeasible (mswProduct.map (Rat.castHom ℝ)) c p)
    (hq : StarFeasible (mswProduct.map (Rat.castHom ℝ)) c q)
    (lp lq : Fin 40 → Fin 80) (hlp : Function.Injective lp) (hlq : Function.Injective lq)
    (hap : ∀ j, (mswProduct.map (Rat.castHom ℝ)) (lp j) ⬝ᵥ p = 0)
    (haq : ∀ j, (mswProduct.map (Rat.castHom ℝ)) (lq j) ⬝ᵥ q = 0)
    (hc : ((univ.image lp) ∩ (univ.image lq)).card = 39) :
    StarCommonFaceSegment (mswProduct.map (Rat.castHom ℝ)) c p q
      (univ.image lp) (univ.image lq) :=
  firstProduct_real_common_face mswIntegralA mswIntegralStarChart
    mswIntegralChart_pivot (by decide) c p q hp0 hq0 hp hq lp lq hlp hlq hap haq (by omega)

/-- The SAME original common labels specify an actual closed segment in
    the FINAL matrix. No new regularity or chart certificate is an input. -/
theorem msw_final_common_face (c : Option (Fin 80)) (p q : Fin 41 → ℝ)
    (hp0 : p 0 = 1) (hq0 : q 0 = 1)
    (hp : StarFeasible (mswFinalMatrix.map (Rat.castHom ℝ)) c p)
    (hq : StarFeasible (mswFinalMatrix.map (Rat.castHom ℝ)) c q)
    (lp lq : Fin 40 → Fin 80) (hlp : Function.Injective lp) (hlq : Function.Injective lq)
    (hap : ∀ j, (mswFinalMatrix.map (Rat.castHom ℝ)) (lp j) ⬝ᵥ p = 0)
    (haq : ∀ j, (mswFinalMatrix.map (Rat.castHom ℝ)) (lq j) ⬝ᵥ q = 0)
    (hc : ((univ.image lp) ∩ (univ.image lq)).card = 39) :
    StarCommonFaceSegment (mswFinalMatrix.map (Rat.castHom ℝ)) c p q
      (univ.image lp) (univ.image lq) :=
  second_real_common_face mswIntegralA mswIntegralStarChart
    mswIntegralChart_pivot (by decide) c p q hp0 hq0 hp hq lp lq hlp hlq hap haq (by omega)

#print axioms msw_product_common_face
#print axioms msw_final_common_face
end
end ADKZPricing
