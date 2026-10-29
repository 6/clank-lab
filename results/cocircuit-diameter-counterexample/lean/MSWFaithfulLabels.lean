import MSWConstruction
import CellSignTransport

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- The actual original MSW product and actual final matrix have the
    same real active vertex labels in ALL81closed cells. Both field
    changes, positive normalizations and chart maps are already discharged. -/
theorem msw_real_product_label_iff (c : Option (Fin 80))
    (label : Fin 40 → Fin 80) (hl : Function.Injective label) :
    ActiveRay (mswFinalMatrix.map (Rat.castHom ℝ)) c label ↔
      ActiveRay (mswProduct.map (Rat.castHom ℝ)) c label :=
  second_product_real_label_iff mswIntegralA mswIntegralStarChart
    mswIntegralChart_pivot (by decide) c label hl

/-- Direct bridge to the frozen full cocircuit definition; no supplied
    graph isomorphism or undisclosed preservation certificate is an input. -/
theorem msw_product_label_cocircuit (c : Option (Fin 80))
    (label : Fin 40 → Fin 80) (hl : Function.Injective label) :
    ActiveRay (mswProduct.map (Rat.castHom ℝ)) c label ↔
      Cocircuit mswFinalMatrix (cellLabelSigns c (univ.image label)) :=
  (msw_real_product_label_iff c label hl).symm.trans
    (uniform_active_cocircuit_iff mswFinalMatrix mswFinal_uniform c label hl)

/-- Faithful full-graph adjacency on actual product-cell labels is
    exactly the original shared39row condition. The endpoints are guarded
    by actual real product-cell membership, not ambient isolated vertices. -/
theorem msw_product_cell_adjacency (c : Option (Fin 80))
    (p q : Fin 40 → Fin 80) (hp : Function.Injective p) (hq : Function.Injective q)
    (hvp : ActiveRay (mswProduct.map (Rat.castHom ℝ)) c p)
    (hvq : ActiveRay (mswProduct.map (Rat.castHom ℝ)) c q) :
    Adjacent mswFinalMatrix (cellLabelSigns c (univ.image p))
      (cellLabelSigns c (univ.image q)) ↔
      ((univ.image p) ∩ (univ.image q)).card = 39 :=
  uniform_cell_adjacency_iff mswFinalMatrix mswFinal_uniform c p q hp hq
    ((msw_real_product_label_iff c p hp).mpr hvp)
    ((msw_real_product_label_iff c q hq).mpr hvq)

#print axioms msw_real_product_label_iff
#print axioms msw_product_label_cocircuit
#print axioms msw_product_cell_adjacency
end
end ADKZPricing
