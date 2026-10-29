import MSWIntegralData
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace ADKZPricing
open Matrix Finset
noncomputable section

theorem msw_chart_column_13 (c : Option (Fin 40)) :
    mswIntegralChartData (13 : Fin 21) =
      ∑ i, mswIntegralWeights c i * (starSign c i * mswIntegralA i (13 : Fin 21)) := by
  have hn (i : Fin 40) : ¬ (none : Option (Fin 40)) = some i := by intro h; cases h
  cases c with
  | none =>
    norm_num [mswIntegralChartData, mswIntegralWeights, mswWeightPredecessors,
      mswIntegralA, starSign, Fin.sum_univ_succ, Matrix.cons_val, Fin.reduceFinMk,
      reduceCtorEq, Option.some.injEq, Fin.mk.injEq, hn]
    all_goals decide
  | some k =>
    fin_cases k <;> norm_num [mswIntegralChartData, mswIntegralWeights,
      mswWeightPredecessors, mswIntegralA, starSign, Fin.sum_univ_succ, Matrix.cons_val, Fin.reduceFinMk,
      reduceCtorEq, Option.some.injEq, Fin.mk.injEq, hn]
    all_goals decide
#print axioms msw_chart_column_13
end
end ADKZPricing
