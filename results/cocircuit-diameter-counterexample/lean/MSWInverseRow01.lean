import MSWIntegralData
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace ADKZPricing
open Matrix Finset
noncomputable section

theorem msw_inverse_row_01 (j : Fin 21) :
    ((mswIntegralA.submatrix mswIntegralBasis id).map (Int.castRingHom ℚ) *
      mswIntegralInverse) (1 : Fin 21) j = (1 : Matrix (Fin 21) (Fin 21) ℚ) 1 j := by
  fin_cases j <;> norm_num [mswIntegralA, mswIntegralBasis, mswIntegralInverse,
    Matrix.mul_apply, Matrix.submatrix, Matrix.map_apply, Matrix.one_apply, Fin.sum_univ_succ,
    Matrix.cons_val, Fin.reduceFinMk, Fin.mk.injEq]
  all_goals decide
#print axioms msw_inverse_row_01
end
end ADKZPricing
