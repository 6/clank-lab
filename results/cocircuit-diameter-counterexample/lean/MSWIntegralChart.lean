import MSWChartColumn00
import MSWInverseRow00
import MSWChartColumn01
import MSWInverseRow01
import MSWChartColumn02
import MSWInverseRow02
import MSWChartColumn03
import MSWInverseRow03
import MSWChartColumn04
import MSWInverseRow04
import MSWChartColumn05
import MSWInverseRow05
import MSWChartColumn06
import MSWInverseRow06
import MSWChartColumn07
import MSWInverseRow07
import MSWChartColumn08
import MSWInverseRow08
import MSWChartColumn09
import MSWInverseRow09
import MSWChartColumn10
import MSWInverseRow10
import MSWChartColumn11
import MSWInverseRow11
import MSWChartColumn12
import MSWInverseRow12
import MSWChartColumn13
import MSWInverseRow13
import MSWChartColumn14
import MSWInverseRow14
import MSWChartColumn15
import MSWInverseRow15
import MSWChartColumn16
import MSWInverseRow16
import MSWChartColumn17
import MSWInverseRow17
import MSWChartColumn18
import MSWInverseRow18
import MSWChartColumn19
import MSWInverseRow19
import MSWChartColumn20
import MSWInverseRow20
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace ADKZPricing
open Matrix Finset
noncomputable section

theorem mswIntegral_representation (c : Option (Fin 40)) (j : Fin 21) :
    mswIntegralChartData j = ∑ i, mswIntegralWeights c i * (starSign c i * mswIntegralA i j) := by
  fin_cases j
  · exact msw_chart_column_00 c
  · exact msw_chart_column_01 c
  · exact msw_chart_column_02 c
  · exact msw_chart_column_03 c
  · exact msw_chart_column_04 c
  · exact msw_chart_column_05 c
  · exact msw_chart_column_06 c
  · exact msw_chart_column_07 c
  · exact msw_chart_column_08 c
  · exact msw_chart_column_09 c
  · exact msw_chart_column_10 c
  · exact msw_chart_column_11 c
  · exact msw_chart_column_12 c
  · exact msw_chart_column_13 c
  · exact msw_chart_column_14 c
  · exact msw_chart_column_15 c
  · exact msw_chart_column_16 c
  · exact msw_chart_column_17 c
  · exact msw_chart_column_18 c
  · exact msw_chart_column_19 c
  · exact msw_chart_column_20 c

theorem mswIntegral_right_inverse :
    (mswIntegralA.submatrix mswIntegralBasis id).map (Int.castRingHom ℚ) * mswIntegralInverse = 1 := by
  ext i j
  fin_cases i
  · exact msw_inverse_row_00 j
  · exact msw_inverse_row_01 j
  · exact msw_inverse_row_02 j
  · exact msw_inverse_row_03 j
  · exact msw_inverse_row_04 j
  · exact msw_inverse_row_05 j
  · exact msw_inverse_row_06 j
  · exact msw_inverse_row_07 j
  · exact msw_inverse_row_08 j
  · exact msw_inverse_row_09 j
  · exact msw_inverse_row_10 j
  · exact msw_inverse_row_11 j
  · exact msw_inverse_row_12 j
  · exact msw_inverse_row_13 j
  · exact msw_inverse_row_14 j
  · exact msw_inverse_row_15 j
  · exact msw_inverse_row_16 j
  · exact msw_inverse_row_17 j
  · exact msw_inverse_row_18 j
  · exact msw_inverse_row_19 j
  · exact msw_inverse_row_20 j

def mswIntegralStarChart : IntegralStarChart mswIntegralA where
  chart := mswIntegralChartData
  weights := mswIntegralWeights
  positive := mswIntegralWeights_positive
  representation := mswIntegral_representation
  basis := mswIntegralBasis
  basis_injective := mswIntegralBasis_injective
  basis_det := integer_det_ne_zero_of_rational_right_inverse _ _ mswIntegral_right_inverse

theorem mswIntegral_positive_scaling (i : Fin 40) (j : Fin 21) :
    (mswIntegralA i j : ℚ) = (mswIntegralRowScales i : ℚ) * mswSource i j := by
  fin_cases i <;> fin_cases j
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (100 : ℚ) = (1 : ℚ) * (100)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (21 : ℚ) = (1 : ℚ) * (21)
    norm_num
  · change (-7 : ℚ) = (1 : ℚ) * (-7)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (100 : ℚ) = (1 : ℚ) * (100)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (16 : ℚ) = (1 : ℚ) * (16)
    norm_num
  · change (-15 : ℚ) = (1 : ℚ) * (-15)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (100 : ℚ) = (1 : ℚ) * (100)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (-32 : ℚ) = (1 : ℚ) * (-32)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (100 : ℚ) = (1 : ℚ) * (100)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (-16 : ℚ) = (1 : ℚ) * (-16)
    norm_num
  · change (-15 : ℚ) = (1 : ℚ) * (-15)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (100 : ℚ) = (1 : ℚ) * (100)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (-21 : ℚ) = (1 : ℚ) * (-21)
    norm_num
  · change (-7 : ℚ) = (1 : ℚ) * (-7)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (100 : ℚ) = (1 : ℚ) * (100)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (-20 : ℚ) = (1 : ℚ) * (-20)
    norm_num
  · change (-4 : ℚ) = (1 : ℚ) * (-4)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (100 : ℚ) = (1 : ℚ) * (100)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (32 : ℚ) = (1 : ℚ) * (32)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (100 : ℚ) = (1 : ℚ) * (100)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (20 : ℚ) = (1 : ℚ) * (20)
    norm_num
  · change (-4 : ℚ) = (1 : ℚ) * (-4)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (100 : ℚ) = (100 : ℚ) * (1)
    norm_num
  · change (10000 : ℚ) = (100 : ℚ) * (100)
    norm_num
  · change (3 : ℚ) = (100 : ℚ) * (3/100)
    norm_num
  · change (-2 : ℚ) = (100 : ℚ) * (-1/50)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (-3000 : ℚ) = (100 : ℚ) * (-30)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (100 : ℚ) = (100 : ℚ) * (1)
    norm_num
  · change (10000 : ℚ) = (100 : ℚ) * (100)
    norm_num
  · change (-3 : ℚ) = (100 : ℚ) * (-3/100)
    norm_num
  · change (-2 : ℚ) = (100 : ℚ) * (-1/50)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (3000 : ℚ) = (100 : ℚ) * (30)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (200000 : ℚ) = (2000 : ℚ) * (100)
    norm_num
  · change (-3 : ℚ) = (2000 : ℚ) * (-3/2000)
    norm_num
  · change (7 : ℚ) = (2000 : ℚ) * (7/2000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (63600 : ℚ) = (2000 : ℚ) * (159/5)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (200000 : ℚ) = (2000 : ℚ) * (100)
    norm_num
  · change (3 : ℚ) = (2000 : ℚ) * (3/2000)
    norm_num
  · change (7 : ℚ) = (2000 : ℚ) * (7/2000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (-63600 : ℚ) = (2000 : ℚ) * (-159/5)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000000 : ℚ) = (2000 : ℚ) * (10000000000)
    norm_num
  · change (200000000000000 : ℚ) = (2000 : ℚ) * (100000000000)
    norm_num
  · change (200000000000000 : ℚ) = (2000 : ℚ) * (100000000000)
    norm_num
  · change (200000000000000 : ℚ) = (2000 : ℚ) * (100000000000)
    norm_num
  · change (200000000000000 : ℚ) = (2000 : ℚ) * (100000000000)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (200000 : ℚ) = (2000 : ℚ) * (100)
    norm_num
  · change (3 : ℚ) = (2000 : ℚ) * (3/2000)
    norm_num
  · change (7 : ℚ) = (2000 : ℚ) * (7/2000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (-63600 : ℚ) = (2000 : ℚ) * (-159/5)
    norm_num
  · change (-20000000000 : ℚ) = (2000 : ℚ) * (-10000000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (200000 : ℚ) = (2000 : ℚ) * (100)
    norm_num
  · change (3 : ℚ) = (2000 : ℚ) * (3/2000)
    norm_num
  · change (7 : ℚ) = (2000 : ℚ) * (7/2000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (-63600 : ℚ) = (2000 : ℚ) * (-159/5)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (-20000000000 : ℚ) = (2000 : ℚ) * (-10000000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (200000 : ℚ) = (2000 : ℚ) * (100)
    norm_num
  · change (3 : ℚ) = (2000 : ℚ) * (3/2000)
    norm_num
  · change (7 : ℚ) = (2000 : ℚ) * (7/2000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (-63600 : ℚ) = (2000 : ℚ) * (-159/5)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (-20000000000 : ℚ) = (2000 : ℚ) * (-10000000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (200000 : ℚ) = (2000 : ℚ) * (100)
    norm_num
  · change (3 : ℚ) = (2000 : ℚ) * (3/2000)
    norm_num
  · change (7 : ℚ) = (2000 : ℚ) * (7/2000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (-63600 : ℚ) = (2000 : ℚ) * (-159/5)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (-20000000000000 : ℚ) = (2000 : ℚ) * (-10000000000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (200000 : ℚ) = (2000 : ℚ) * (100)
    norm_num
  · change (3 : ℚ) = (2000 : ℚ) * (3/2000)
    norm_num
  · change (7 : ℚ) = (2000 : ℚ) * (7/2000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (-63600 : ℚ) = (2000 : ℚ) * (-159/5)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000000 : ℚ) = (2000 : ℚ) * (10000000000)
    norm_num
  · change (-200000000000000 : ℚ) = (2000 : ℚ) * (-100000000000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (200000 : ℚ) = (2000 : ℚ) * (100)
    norm_num
  · change (3 : ℚ) = (2000 : ℚ) * (3/2000)
    norm_num
  · change (7 : ℚ) = (2000 : ℚ) * (7/2000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (-63600 : ℚ) = (2000 : ℚ) * (-159/5)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000000 : ℚ) = (2000 : ℚ) * (10000000000)
    norm_num
  · change (200000000000000 : ℚ) = (2000 : ℚ) * (100000000000)
    norm_num
  · change (-200000000000000 : ℚ) = (2000 : ℚ) * (-100000000000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (200000 : ℚ) = (2000 : ℚ) * (100)
    norm_num
  · change (3 : ℚ) = (2000 : ℚ) * (3/2000)
    norm_num
  · change (7 : ℚ) = (2000 : ℚ) * (7/2000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (-63600 : ℚ) = (2000 : ℚ) * (-159/5)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000000 : ℚ) = (2000 : ℚ) * (10000000000)
    norm_num
  · change (200000000000000 : ℚ) = (2000 : ℚ) * (100000000000)
    norm_num
  · change (200000000000000 : ℚ) = (2000 : ℚ) * (100000000000)
    norm_num
  · change (-200000000000000 : ℚ) = (2000 : ℚ) * (-100000000000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (200000 : ℚ) = (2000 : ℚ) * (100)
    norm_num
  · change (3 : ℚ) = (2000 : ℚ) * (3/2000)
    norm_num
  · change (7 : ℚ) = (2000 : ℚ) * (7/2000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (-63600 : ℚ) = (2000 : ℚ) * (-159/5)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000000 : ℚ) = (2000 : ℚ) * (10000000000)
    norm_num
  · change (200000000000000 : ℚ) = (2000 : ℚ) * (100000000000)
    norm_num
  · change (200000000000000 : ℚ) = (2000 : ℚ) * (100000000000)
    norm_num
  · change (200000000000000 : ℚ) = (2000 : ℚ) * (100000000000)
    norm_num
  · change (-200000000000000 : ℚ) = (2000 : ℚ) * (-100000000000)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (-100 : ℚ) = (1 : ℚ) * (-100)
    norm_num
  · change (30 : ℚ) = (1 : ℚ) * (30)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (-100 : ℚ) = (1 : ℚ) * (-100)
    norm_num
  · change (4 : ℚ) = (1 : ℚ) * (4)
    norm_num
  · change (-15 : ℚ) = (1 : ℚ) * (-15)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (2 : ℚ) = (2 : ℚ) * (1)
    norm_num
  · change (-200 : ℚ) = (2 : ℚ) * (-100)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (-33 : ℚ) = (2 : ℚ) * (-33/2)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (2 : ℚ) = (2 : ℚ) * (1)
    norm_num
  · change (2 : ℚ) = (2 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (-100 : ℚ) = (1 : ℚ) * (-100)
    norm_num
  · change (-1 : ℚ) = (1 : ℚ) * (-1)
    norm_num
  · change (-16 : ℚ) = (1 : ℚ) * (-16)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (2 : ℚ) = (2 : ℚ) * (1)
    norm_num
  · change (-200 : ℚ) = (2 : ℚ) * (-100)
    norm_num
  · change (-55 : ℚ) = (2 : ℚ) * (-55/2)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (2 : ℚ) = (2 : ℚ) * (1)
    norm_num
  · change (2 : ℚ) = (2 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (-100 : ℚ) = (1 : ℚ) * (-100)
    norm_num
  · change (-17 : ℚ) = (1 : ℚ) * (-17)
    norm_num
  · change (18 : ℚ) = (1 : ℚ) * (18)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (-100 : ℚ) = (1 : ℚ) * (-100)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (38 : ℚ) = (1 : ℚ) * (38)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (1 : ℚ) * (1)
    norm_num
  · change (-100 : ℚ) = (1 : ℚ) * (-100)
    norm_num
  · change (22 : ℚ) = (1 : ℚ) * (22)
    norm_num
  · change (17 : ℚ) = (1 : ℚ) * (17)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (1 : ℚ) * (0)
    norm_num
  · change (5 : ℚ) = (5 : ℚ) * (1)
    norm_num
  · change (-500 : ℚ) = (5 : ℚ) * (-100)
    norm_num
  · change (-50 : ℚ) = (5 : ℚ) * (-10)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (1 : ℚ) = (5 : ℚ) * (1/5)
    norm_num
  · change (-1 : ℚ) = (5 : ℚ) * (-1/5)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (5 : ℚ) * (0)
    norm_num
  · change (100 : ℚ) = (100 : ℚ) * (1)
    norm_num
  · change (-10000 : ℚ) = (100 : ℚ) * (-100)
    norm_num
  · change (2999 : ℚ) = (100 : ℚ) * (2999/100)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (-12 : ℚ) = (100 : ℚ) * (-3/25)
    norm_num
  · change (-20 : ℚ) = (100 : ℚ) * (-1/5)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (100 : ℚ) = (100 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (100 : ℚ) * (0)
    norm_num
  · change (10000 : ℚ) = (10000 : ℚ) * (1)
    norm_num
  · change (-1000000 : ℚ) = (10000 : ℚ) * (-100)
    norm_num
  · change (299999 : ℚ) = (10000 : ℚ) * (299999/10000)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (100 : ℚ) = (10000 : ℚ) * (1/100)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (10000 : ℚ) = (10000 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (10000 : ℚ) * (0)
    norm_num
  · change (20000 : ℚ) = (20000 : ℚ) * (1)
    norm_num
  · change (-2000000 : ℚ) = (20000 : ℚ) * (-100)
    norm_num
  · change (-549000 : ℚ) = (20000 : ℚ) * (-549/20)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (4 : ℚ) = (20000 : ℚ) * (1/5000)
    norm_num
  · change (25 : ℚ) = (20000 : ℚ) * (1/800)
    norm_num
  · change (20000 : ℚ) = (20000 : ℚ) * (1)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (20000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (-200000 : ℚ) = (2000 : ℚ) * (-100)
    norm_num
  · change (-54000 : ℚ) = (2000 : ℚ) * (-27)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (4 : ℚ) = (2000 : ℚ) * (1/500)
    norm_num
  · change (-25 : ℚ) = (2000 : ℚ) * (-1/80)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (200000000 : ℚ) = (2000 : ℚ) * (100000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (200000000000 : ℚ) = (2000 : ℚ) * (100000000)
    norm_num
  · change (200000000000 : ℚ) = (2000 : ℚ) * (100000000)
    norm_num
  · change (2000000000000 : ℚ) = (2000 : ℚ) * (1000000000)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (-200000 : ℚ) = (2000 : ℚ) * (-100)
    norm_num
  · change (-54000 : ℚ) = (2000 : ℚ) * (-27)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (4 : ℚ) = (2000 : ℚ) * (1/500)
    norm_num
  · change (-25 : ℚ) = (2000 : ℚ) * (-1/80)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (-200000000 : ℚ) = (2000 : ℚ) * (-100000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (-200000 : ℚ) = (2000 : ℚ) * (-100)
    norm_num
  · change (-54000 : ℚ) = (2000 : ℚ) * (-27)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (4 : ℚ) = (2000 : ℚ) * (1/500)
    norm_num
  · change (-25 : ℚ) = (2000 : ℚ) * (-1/80)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (200000000 : ℚ) = (2000 : ℚ) * (100000)
    norm_num
  · change (-20000000000 : ℚ) = (2000 : ℚ) * (-10000000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (-200000 : ℚ) = (2000 : ℚ) * (-100)
    norm_num
  · change (-54000 : ℚ) = (2000 : ℚ) * (-27)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (4 : ℚ) = (2000 : ℚ) * (1/500)
    norm_num
  · change (-25 : ℚ) = (2000 : ℚ) * (-1/80)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (200000000 : ℚ) = (2000 : ℚ) * (100000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (-20000000000 : ℚ) = (2000 : ℚ) * (-10000000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (-200000 : ℚ) = (2000 : ℚ) * (-100)
    norm_num
  · change (-54000 : ℚ) = (2000 : ℚ) * (-27)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (4 : ℚ) = (2000 : ℚ) * (1/500)
    norm_num
  · change (-25 : ℚ) = (2000 : ℚ) * (-1/80)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (200000000 : ℚ) = (2000 : ℚ) * (100000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (-20000000000 : ℚ) = (2000 : ℚ) * (-10000000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (-200000 : ℚ) = (2000 : ℚ) * (-100)
    norm_num
  · change (-54000 : ℚ) = (2000 : ℚ) * (-27)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (4 : ℚ) = (2000 : ℚ) * (1/500)
    norm_num
  · change (-25 : ℚ) = (2000 : ℚ) * (-1/80)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (200000000 : ℚ) = (2000 : ℚ) * (100000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (-200000000000 : ℚ) = (2000 : ℚ) * (-100000000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (-200000 : ℚ) = (2000 : ℚ) * (-100)
    norm_num
  · change (-54000 : ℚ) = (2000 : ℚ) * (-27)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (4 : ℚ) = (2000 : ℚ) * (1/500)
    norm_num
  · change (-25 : ℚ) = (2000 : ℚ) * (-1/80)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (200000000 : ℚ) = (2000 : ℚ) * (100000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (200000000000 : ℚ) = (2000 : ℚ) * (100000000)
    norm_num
  · change (-200000000000 : ℚ) = (2000 : ℚ) * (-100000000)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (2000 : ℚ) = (2000 : ℚ) * (1)
    norm_num
  · change (-200000 : ℚ) = (2000 : ℚ) * (-100)
    norm_num
  · change (-54000 : ℚ) = (2000 : ℚ) * (-27)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (4 : ℚ) = (2000 : ℚ) * (1/500)
    norm_num
  · change (-25 : ℚ) = (2000 : ℚ) * (-1/80)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (0 : ℚ) = (2000 : ℚ) * (0)
    norm_num
  · change (200000000 : ℚ) = (2000 : ℚ) * (100000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (20000000000 : ℚ) = (2000 : ℚ) * (10000000)
    norm_num
  · change (200000000000 : ℚ) = (2000 : ℚ) * (100000000)
    norm_num
  · change (200000000000 : ℚ) = (2000 : ℚ) * (100000000)
    norm_num
  · change (-2000000000000 : ℚ) = (2000 : ℚ) * (-1000000000)
    norm_num


theorem mswIntegral_scales_positive (i : Fin 40) : 0 < mswIntegralRowScales i := by
  fin_cases i <;> norm_num [mswIntegralRowScales]

#print axioms mswIntegralStarChart
#print axioms mswIntegral_positive_scaling
#print axioms mswIntegral_scales_positive
end
end ADKZPricing
