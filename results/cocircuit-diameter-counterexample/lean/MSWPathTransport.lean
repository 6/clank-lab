import MSWConstruction
import FullGraphCellTransport
import SecondChartWalk

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- Fold and instantiate final real regularity before the concrete80/41
    specialization, using the actual original chart certificate. -/
theorem second_real_regular_chart {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (c : Option (Fin (n + n))) :
    RegularChart ((secondPerturbedMatrix A C h0).map (Rat.castHom ℝ)) c := by
  have hp := chartedGenericFactor_real_properties _ _ (secondIntegralChart_pivot A C h0)
  exact uniform_regular_chart _ hp.1 c (hp.2 c)

theorem mswFinal_regular_chart (c : Option (Fin 80)) :
    RegularChart (mswFinalMatrix.map (Rat.castHom ℝ)) c :=
  second_real_regular_chart mswIntegralA mswIntegralStarChart mswIntegralChart_pivot c

/-- Every short walk in the faithful FULL frozen cocircuit graph of the
    actual final matrix transports to the literal union of two actual
    product cell graphs. ONE exceptional original row is fixed for the
    whole path; one map retains all shared vertices and edges. -/
theorem msw_short_walk_product_union (X Y : SignVector)
    (hcomp : Complementary X Y) (hw : ShortWalk mswFinalMatrix X Y) :
    ∃ L : ℕ, L ≤ 41 ∧ ∃ e : Fin 80,
      let F := mswFirstFactor.map (Rat.castHom ℝ)
      LabelledCell.CellWalk (LabelledCell.union (productChartCell F F none)
        (productChartCell F F (some e)))
        (productLabelPair (signZeros X)) (productLabelPair (signZeros Y)) L := by
  obtain ⟨L, hL, e, hwalk⟩ := full_short_walk_chart_union mswFinalMatrix mswFinal_uniform
    mswFinal_regular_chart X Y hcomp hw
  exact ⟨L, hL, e, second_union_pair_walk mswIntegralA mswIntegralStarChart
    mswIntegralChart_pivot (by decide) none (some e) hwalk⟩

#print axioms mswFinal_regular_chart
#print axioms msw_short_walk_product_union
end
end ADKZPricing
