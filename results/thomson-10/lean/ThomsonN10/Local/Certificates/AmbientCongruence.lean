/- Adapted from proof/ambient_circuit/export_lean_congruence.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientCongruenceChecks00
import ThomsonN10.Local.Certificates.AmbientCongruenceChecks01
import ThomsonN10.Local.Certificates.AmbientCongruenceChecks02
import ThomsonN10.Local.Certificates.AmbientCongruenceChecks03
import ThomsonN10.Local.Certificates.AmbientCongruenceChecks04
import ThomsonN10.Local.Certificates.AmbientCongruenceChecks05
import ThomsonN10.Local.Certificates.AmbientCongruenceChecks06
import ThomsonN10.Local.Certificates.AmbientCongruenceChecks07
import ThomsonN10.Local.Certificates.AmbientCongruenceChecks08
import ThomsonN10.Local.Certificates.AmbientCongruenceChecks09
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def firstRecipes (i j : ℕ) : DotRecipe :=
  (#[firstRecipesRow0,firstRecipesRow1,firstRecipesRow2,firstRecipesRow3,firstRecipesRow4,firstRecipesRow5,firstRecipesRow6,firstRecipesRow7,firstRecipesRow8,firstRecipesRow9,firstRecipesRow10,firstRecipesRow11,firstRecipesRow12,firstRecipesRow13,firstRecipesRow14,firstRecipesRow15,firstRecipesRow16,firstRecipesRow17,firstRecipesRow18,firstRecipesRow19,firstRecipesRow20,firstRecipesRow21,firstRecipesRow22,firstRecipesRow23,firstRecipesRow24,firstRecipesRow25,firstRecipesRow26,firstRecipesRow27,firstRecipesRow28,firstRecipesRow29][i]?.getD #[])[j]?.getD emptyDotRecipe
theorem first_recipes_checked (i j : Fin 30) : (firstRecipes i j).Check nodes 30 := by
  fin_cases i
  · exact firstRecipesRow0_checked j
  · exact firstRecipesRow1_checked j
  · exact firstRecipesRow2_checked j
  · exact firstRecipesRow3_checked j
  · exact firstRecipesRow4_checked j
  · exact firstRecipesRow5_checked j
  · exact firstRecipesRow6_checked j
  · exact firstRecipesRow7_checked j
  · exact firstRecipesRow8_checked j
  · exact firstRecipesRow9_checked j
  · exact firstRecipesRow10_checked j
  · exact firstRecipesRow11_checked j
  · exact firstRecipesRow12_checked j
  · exact firstRecipesRow13_checked j
  · exact firstRecipesRow14_checked j
  · exact firstRecipesRow15_checked j
  · exact firstRecipesRow16_checked j
  · exact firstRecipesRow17_checked j
  · exact firstRecipesRow18_checked j
  · exact firstRecipesRow19_checked j
  · exact firstRecipesRow20_checked j
  · exact firstRecipesRow21_checked j
  · exact firstRecipesRow22_checked j
  · exact firstRecipesRow23_checked j
  · exact firstRecipesRow24_checked j
  · exact firstRecipesRow25_checked j
  · exact firstRecipesRow26_checked j
  · exact firstRecipesRow27_checked j
  · exact firstRecipesRow28_checked j
  · exact firstRecipesRow29_checked j
theorem first_left_row0 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 0 j).left k = hessianIndices 0 k := by
  revert j k
  decide
theorem first_left_row1 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 1 j).left k = hessianIndices 1 k := by
  revert j k
  decide
theorem first_left_row2 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 2 j).left k = hessianIndices 2 k := by
  revert j k
  decide
theorem first_left_row3 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 3 j).left k = hessianIndices 3 k := by
  revert j k
  decide
theorem first_left_row4 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 4 j).left k = hessianIndices 4 k := by
  revert j k
  decide
theorem first_left_row5 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 5 j).left k = hessianIndices 5 k := by
  revert j k
  decide
theorem first_left_row6 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 6 j).left k = hessianIndices 6 k := by
  revert j k
  decide
theorem first_left_row7 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 7 j).left k = hessianIndices 7 k := by
  revert j k
  decide
theorem first_left_row8 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 8 j).left k = hessianIndices 8 k := by
  revert j k
  decide
theorem first_left_row9 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 9 j).left k = hessianIndices 9 k := by
  revert j k
  decide
theorem first_left_row10 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 10 j).left k = hessianIndices 10 k := by
  revert j k
  decide
theorem first_left_row11 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 11 j).left k = hessianIndices 11 k := by
  revert j k
  decide
theorem first_left_row12 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 12 j).left k = hessianIndices 12 k := by
  revert j k
  decide
theorem first_left_row13 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 13 j).left k = hessianIndices 13 k := by
  revert j k
  decide
theorem first_left_row14 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 14 j).left k = hessianIndices 14 k := by
  revert j k
  decide
theorem first_left_row15 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 15 j).left k = hessianIndices 15 k := by
  revert j k
  decide
theorem first_left_row16 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 16 j).left k = hessianIndices 16 k := by
  revert j k
  decide
theorem first_left_row17 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 17 j).left k = hessianIndices 17 k := by
  revert j k
  decide
theorem first_left_row18 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 18 j).left k = hessianIndices 18 k := by
  revert j k
  decide
theorem first_left_row19 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 19 j).left k = hessianIndices 19 k := by
  revert j k
  decide
theorem first_left_row20 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 20 j).left k = hessianIndices 20 k := by
  revert j k
  decide
theorem first_left_row21 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 21 j).left k = hessianIndices 21 k := by
  revert j k
  decide
theorem first_left_row22 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 22 j).left k = hessianIndices 22 k := by
  revert j k
  decide
theorem first_left_row23 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 23 j).left k = hessianIndices 23 k := by
  revert j k
  decide
theorem first_left_row24 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 24 j).left k = hessianIndices 24 k := by
  revert j k
  decide
theorem first_left_row25 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 25 j).left k = hessianIndices 25 k := by
  revert j k
  decide
theorem first_left_row26 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 26 j).left k = hessianIndices 26 k := by
  revert j k
  decide
theorem first_left_row27 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 27 j).left k = hessianIndices 27 k := by
  revert j k
  decide
theorem first_left_row28 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 28 j).left k = hessianIndices 28 k := by
  revert j k
  decide
theorem first_left_row29 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 29 j).left k = hessianIndices 29 k := by
  revert j k
  decide
theorem first_left (i j : Fin 30) (k : Fin 30) :
    (firstRecipes i j).left k = hessianIndices i k := by
  fin_cases i
  · exact first_left_row0 j k
  · exact first_left_row1 j k
  · exact first_left_row2 j k
  · exact first_left_row3 j k
  · exact first_left_row4 j k
  · exact first_left_row5 j k
  · exact first_left_row6 j k
  · exact first_left_row7 j k
  · exact first_left_row8 j k
  · exact first_left_row9 j k
  · exact first_left_row10 j k
  · exact first_left_row11 j k
  · exact first_left_row12 j k
  · exact first_left_row13 j k
  · exact first_left_row14 j k
  · exact first_left_row15 j k
  · exact first_left_row16 j k
  · exact first_left_row17 j k
  · exact first_left_row18 j k
  · exact first_left_row19 j k
  · exact first_left_row20 j k
  · exact first_left_row21 j k
  · exact first_left_row22 j k
  · exact first_left_row23 j k
  · exact first_left_row24 j k
  · exact first_left_row25 j k
  · exact first_left_row26 j k
  · exact first_left_row27 j k
  · exact first_left_row28 j k
  · exact first_left_row29 j k
theorem first_right_row0 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 0 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row1 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 1 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row2 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 2 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row3 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 3 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row4 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 4 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row5 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 5 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row6 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 6 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row7 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 7 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row8 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 8 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row9 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 9 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row10 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 10 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row11 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 11 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row12 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 12 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row13 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 13 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row14 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 14 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row15 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 15 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row16 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 16 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row17 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 17 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row18 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 18 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row19 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 19 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row20 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 20 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row21 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 21 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row22 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 22 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row23 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 23 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row24 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 24 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row25 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 25 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row26 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 26 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row27 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 27 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row28 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 28 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right_row29 (j : Fin 30) (k : Fin 30) :
    (firstRecipes 29 j).right k = congruenceIndices k j := by
  revert j k
  decide
theorem first_right (i j : Fin 30) (k : Fin 30) :
    (firstRecipes i j).right k = congruenceIndices k j := by
  fin_cases i
  · exact first_right_row0 j k
  · exact first_right_row1 j k
  · exact first_right_row2 j k
  · exact first_right_row3 j k
  · exact first_right_row4 j k
  · exact first_right_row5 j k
  · exact first_right_row6 j k
  · exact first_right_row7 j k
  · exact first_right_row8 j k
  · exact first_right_row9 j k
  · exact first_right_row10 j k
  · exact first_right_row11 j k
  · exact first_right_row12 j k
  · exact first_right_row13 j k
  · exact first_right_row14 j k
  · exact first_right_row15 j k
  · exact first_right_row16 j k
  · exact first_right_row17 j k
  · exact first_right_row18 j k
  · exact first_right_row19 j k
  · exact first_right_row20 j k
  · exact first_right_row21 j k
  · exact first_right_row22 j k
  · exact first_right_row23 j k
  · exact first_right_row24 j k
  · exact first_right_row25 j k
  · exact first_right_row26 j k
  · exact first_right_row27 j k
  · exact first_right_row28 j k
  · exact first_right_row29 j k
theorem first_accumulator_row0 (j : Fin 30) :
    (firstRecipes 0 j).accumulator 30 = firstProductIndices 0 j := by
  revert j
  decide
theorem first_accumulator_row1 (j : Fin 30) :
    (firstRecipes 1 j).accumulator 30 = firstProductIndices 1 j := by
  revert j
  decide
theorem first_accumulator_row2 (j : Fin 30) :
    (firstRecipes 2 j).accumulator 30 = firstProductIndices 2 j := by
  revert j
  decide
theorem first_accumulator_row3 (j : Fin 30) :
    (firstRecipes 3 j).accumulator 30 = firstProductIndices 3 j := by
  revert j
  decide
theorem first_accumulator_row4 (j : Fin 30) :
    (firstRecipes 4 j).accumulator 30 = firstProductIndices 4 j := by
  revert j
  decide
theorem first_accumulator_row5 (j : Fin 30) :
    (firstRecipes 5 j).accumulator 30 = firstProductIndices 5 j := by
  revert j
  decide
theorem first_accumulator_row6 (j : Fin 30) :
    (firstRecipes 6 j).accumulator 30 = firstProductIndices 6 j := by
  revert j
  decide
theorem first_accumulator_row7 (j : Fin 30) :
    (firstRecipes 7 j).accumulator 30 = firstProductIndices 7 j := by
  revert j
  decide
theorem first_accumulator_row8 (j : Fin 30) :
    (firstRecipes 8 j).accumulator 30 = firstProductIndices 8 j := by
  revert j
  decide
theorem first_accumulator_row9 (j : Fin 30) :
    (firstRecipes 9 j).accumulator 30 = firstProductIndices 9 j := by
  revert j
  decide
theorem first_accumulator_row10 (j : Fin 30) :
    (firstRecipes 10 j).accumulator 30 = firstProductIndices 10 j := by
  revert j
  decide
theorem first_accumulator_row11 (j : Fin 30) :
    (firstRecipes 11 j).accumulator 30 = firstProductIndices 11 j := by
  revert j
  decide
theorem first_accumulator_row12 (j : Fin 30) :
    (firstRecipes 12 j).accumulator 30 = firstProductIndices 12 j := by
  revert j
  decide
theorem first_accumulator_row13 (j : Fin 30) :
    (firstRecipes 13 j).accumulator 30 = firstProductIndices 13 j := by
  revert j
  decide
theorem first_accumulator_row14 (j : Fin 30) :
    (firstRecipes 14 j).accumulator 30 = firstProductIndices 14 j := by
  revert j
  decide
theorem first_accumulator_row15 (j : Fin 30) :
    (firstRecipes 15 j).accumulator 30 = firstProductIndices 15 j := by
  revert j
  decide
theorem first_accumulator_row16 (j : Fin 30) :
    (firstRecipes 16 j).accumulator 30 = firstProductIndices 16 j := by
  revert j
  decide
theorem first_accumulator_row17 (j : Fin 30) :
    (firstRecipes 17 j).accumulator 30 = firstProductIndices 17 j := by
  revert j
  decide
theorem first_accumulator_row18 (j : Fin 30) :
    (firstRecipes 18 j).accumulator 30 = firstProductIndices 18 j := by
  revert j
  decide
theorem first_accumulator_row19 (j : Fin 30) :
    (firstRecipes 19 j).accumulator 30 = firstProductIndices 19 j := by
  revert j
  decide
theorem first_accumulator_row20 (j : Fin 30) :
    (firstRecipes 20 j).accumulator 30 = firstProductIndices 20 j := by
  revert j
  decide
theorem first_accumulator_row21 (j : Fin 30) :
    (firstRecipes 21 j).accumulator 30 = firstProductIndices 21 j := by
  revert j
  decide
theorem first_accumulator_row22 (j : Fin 30) :
    (firstRecipes 22 j).accumulator 30 = firstProductIndices 22 j := by
  revert j
  decide
theorem first_accumulator_row23 (j : Fin 30) :
    (firstRecipes 23 j).accumulator 30 = firstProductIndices 23 j := by
  revert j
  decide
theorem first_accumulator_row24 (j : Fin 30) :
    (firstRecipes 24 j).accumulator 30 = firstProductIndices 24 j := by
  revert j
  decide
theorem first_accumulator_row25 (j : Fin 30) :
    (firstRecipes 25 j).accumulator 30 = firstProductIndices 25 j := by
  revert j
  decide
theorem first_accumulator_row26 (j : Fin 30) :
    (firstRecipes 26 j).accumulator 30 = firstProductIndices 26 j := by
  revert j
  decide
theorem first_accumulator_row27 (j : Fin 30) :
    (firstRecipes 27 j).accumulator 30 = firstProductIndices 27 j := by
  revert j
  decide
theorem first_accumulator_row28 (j : Fin 30) :
    (firstRecipes 28 j).accumulator 30 = firstProductIndices 28 j := by
  revert j
  decide
theorem first_accumulator_row29 (j : Fin 30) :
    (firstRecipes 29 j).accumulator 30 = firstProductIndices 29 j := by
  revert j
  decide
theorem first_accumulator (i j : Fin 30) :
    (firstRecipes i j).accumulator 30 = firstProductIndices i j := by
  fin_cases i
  · exact first_accumulator_row0 j
  · exact first_accumulator_row1 j
  · exact first_accumulator_row2 j
  · exact first_accumulator_row3 j
  · exact first_accumulator_row4 j
  · exact first_accumulator_row5 j
  · exact first_accumulator_row6 j
  · exact first_accumulator_row7 j
  · exact first_accumulator_row8 j
  · exact first_accumulator_row9 j
  · exact first_accumulator_row10 j
  · exact first_accumulator_row11 j
  · exact first_accumulator_row12 j
  · exact first_accumulator_row13 j
  · exact first_accumulator_row14 j
  · exact first_accumulator_row15 j
  · exact first_accumulator_row16 j
  · exact first_accumulator_row17 j
  · exact first_accumulator_row18 j
  · exact first_accumulator_row19 j
  · exact first_accumulator_row20 j
  · exact first_accumulator_row21 j
  · exact first_accumulator_row22 j
  · exact first_accumulator_row23 j
  · exact first_accumulator_row24 j
  · exact first_accumulator_row25 j
  · exact first_accumulator_row26 j
  · exact first_accumulator_row27 j
  · exact first_accumulator_row28 j
  · exact first_accumulator_row29 j
theorem first_matrix_product (values : ℕ → ℝ) :
    matrixValues (value values nodes) 30 firstProductIndices =
      matrixValues (value values nodes) 30 hessianIndices *
        matrixValues (value values nodes) 30 congruenceIndices :=
  matrix_product_recipe_sound values nodes 30 _ _ _ _ first_recipes_checked
    first_left first_right first_accumulator
def secondRecipes (i j : ℕ) : DotRecipe :=
  (#[secondRecipesRow0,secondRecipesRow1,secondRecipesRow2,secondRecipesRow3,secondRecipesRow4,secondRecipesRow5,secondRecipesRow6,secondRecipesRow7,secondRecipesRow8,secondRecipesRow9,secondRecipesRow10,secondRecipesRow11,secondRecipesRow12,secondRecipesRow13,secondRecipesRow14,secondRecipesRow15,secondRecipesRow16,secondRecipesRow17,secondRecipesRow18,secondRecipesRow19,secondRecipesRow20,secondRecipesRow21,secondRecipesRow22,secondRecipesRow23,secondRecipesRow24,secondRecipesRow25,secondRecipesRow26,secondRecipesRow27,secondRecipesRow28,secondRecipesRow29][i]?.getD #[])[j]?.getD emptyDotRecipe
theorem second_recipes_checked (i j : Fin 30) : (secondRecipes i j).Check nodes 30 := by
  fin_cases i
  · exact secondRecipesRow0_checked j
  · exact secondRecipesRow1_checked j
  · exact secondRecipesRow2_checked j
  · exact secondRecipesRow3_checked j
  · exact secondRecipesRow4_checked j
  · exact secondRecipesRow5_checked j
  · exact secondRecipesRow6_checked j
  · exact secondRecipesRow7_checked j
  · exact secondRecipesRow8_checked j
  · exact secondRecipesRow9_checked j
  · exact secondRecipesRow10_checked j
  · exact secondRecipesRow11_checked j
  · exact secondRecipesRow12_checked j
  · exact secondRecipesRow13_checked j
  · exact secondRecipesRow14_checked j
  · exact secondRecipesRow15_checked j
  · exact secondRecipesRow16_checked j
  · exact secondRecipesRow17_checked j
  · exact secondRecipesRow18_checked j
  · exact secondRecipesRow19_checked j
  · exact secondRecipesRow20_checked j
  · exact secondRecipesRow21_checked j
  · exact secondRecipesRow22_checked j
  · exact secondRecipesRow23_checked j
  · exact secondRecipesRow24_checked j
  · exact secondRecipesRow25_checked j
  · exact secondRecipesRow26_checked j
  · exact secondRecipesRow27_checked j
  · exact secondRecipesRow28_checked j
  · exact secondRecipesRow29_checked j
theorem second_left_row0 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 0 j).left k = congruenceIndices k 0 := by
  revert j k
  decide
theorem second_left_row1 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 1 j).left k = congruenceIndices k 1 := by
  revert j k
  decide
theorem second_left_row2 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 2 j).left k = congruenceIndices k 2 := by
  revert j k
  decide
theorem second_left_row3 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 3 j).left k = congruenceIndices k 3 := by
  revert j k
  decide
theorem second_left_row4 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 4 j).left k = congruenceIndices k 4 := by
  revert j k
  decide
theorem second_left_row5 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 5 j).left k = congruenceIndices k 5 := by
  revert j k
  decide
theorem second_left_row6 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 6 j).left k = congruenceIndices k 6 := by
  revert j k
  decide
theorem second_left_row7 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 7 j).left k = congruenceIndices k 7 := by
  revert j k
  decide
theorem second_left_row8 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 8 j).left k = congruenceIndices k 8 := by
  revert j k
  decide
theorem second_left_row9 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 9 j).left k = congruenceIndices k 9 := by
  revert j k
  decide
theorem second_left_row10 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 10 j).left k = congruenceIndices k 10 := by
  revert j k
  decide
theorem second_left_row11 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 11 j).left k = congruenceIndices k 11 := by
  revert j k
  decide
theorem second_left_row12 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 12 j).left k = congruenceIndices k 12 := by
  revert j k
  decide
theorem second_left_row13 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 13 j).left k = congruenceIndices k 13 := by
  revert j k
  decide
theorem second_left_row14 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 14 j).left k = congruenceIndices k 14 := by
  revert j k
  decide
theorem second_left_row15 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 15 j).left k = congruenceIndices k 15 := by
  revert j k
  decide
theorem second_left_row16 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 16 j).left k = congruenceIndices k 16 := by
  revert j k
  decide
theorem second_left_row17 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 17 j).left k = congruenceIndices k 17 := by
  revert j k
  decide
theorem second_left_row18 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 18 j).left k = congruenceIndices k 18 := by
  revert j k
  decide
theorem second_left_row19 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 19 j).left k = congruenceIndices k 19 := by
  revert j k
  decide
theorem second_left_row20 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 20 j).left k = congruenceIndices k 20 := by
  revert j k
  decide
theorem second_left_row21 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 21 j).left k = congruenceIndices k 21 := by
  revert j k
  decide
theorem second_left_row22 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 22 j).left k = congruenceIndices k 22 := by
  revert j k
  decide
theorem second_left_row23 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 23 j).left k = congruenceIndices k 23 := by
  revert j k
  decide
theorem second_left_row24 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 24 j).left k = congruenceIndices k 24 := by
  revert j k
  decide
theorem second_left_row25 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 25 j).left k = congruenceIndices k 25 := by
  revert j k
  decide
theorem second_left_row26 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 26 j).left k = congruenceIndices k 26 := by
  revert j k
  decide
theorem second_left_row27 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 27 j).left k = congruenceIndices k 27 := by
  revert j k
  decide
theorem second_left_row28 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 28 j).left k = congruenceIndices k 28 := by
  revert j k
  decide
theorem second_left_row29 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 29 j).left k = congruenceIndices k 29 := by
  revert j k
  decide
theorem second_left (i j : Fin 30) (k : Fin 30) :
    (secondRecipes i j).left k = congruenceIndices k i := by
  fin_cases i
  · exact second_left_row0 j k
  · exact second_left_row1 j k
  · exact second_left_row2 j k
  · exact second_left_row3 j k
  · exact second_left_row4 j k
  · exact second_left_row5 j k
  · exact second_left_row6 j k
  · exact second_left_row7 j k
  · exact second_left_row8 j k
  · exact second_left_row9 j k
  · exact second_left_row10 j k
  · exact second_left_row11 j k
  · exact second_left_row12 j k
  · exact second_left_row13 j k
  · exact second_left_row14 j k
  · exact second_left_row15 j k
  · exact second_left_row16 j k
  · exact second_left_row17 j k
  · exact second_left_row18 j k
  · exact second_left_row19 j k
  · exact second_left_row20 j k
  · exact second_left_row21 j k
  · exact second_left_row22 j k
  · exact second_left_row23 j k
  · exact second_left_row24 j k
  · exact second_left_row25 j k
  · exact second_left_row26 j k
  · exact second_left_row27 j k
  · exact second_left_row28 j k
  · exact second_left_row29 j k
theorem second_right_row0 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 0 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row1 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 1 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row2 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 2 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row3 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 3 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row4 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 4 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row5 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 5 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row6 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 6 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row7 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 7 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row8 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 8 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row9 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 9 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row10 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 10 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row11 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 11 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row12 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 12 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row13 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 13 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row14 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 14 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row15 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 15 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row16 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 16 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row17 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 17 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row18 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 18 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row19 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 19 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row20 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 20 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row21 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 21 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row22 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 22 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row23 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 23 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row24 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 24 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row25 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 25 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row26 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 26 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row27 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 27 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row28 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 28 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right_row29 (j : Fin 30) (k : Fin 30) :
    (secondRecipes 29 j).right k = firstProductIndices k j := by
  revert j k
  decide
theorem second_right (i j : Fin 30) (k : Fin 30) :
    (secondRecipes i j).right k = firstProductIndices k j := by
  fin_cases i
  · exact second_right_row0 j k
  · exact second_right_row1 j k
  · exact second_right_row2 j k
  · exact second_right_row3 j k
  · exact second_right_row4 j k
  · exact second_right_row5 j k
  · exact second_right_row6 j k
  · exact second_right_row7 j k
  · exact second_right_row8 j k
  · exact second_right_row9 j k
  · exact second_right_row10 j k
  · exact second_right_row11 j k
  · exact second_right_row12 j k
  · exact second_right_row13 j k
  · exact second_right_row14 j k
  · exact second_right_row15 j k
  · exact second_right_row16 j k
  · exact second_right_row17 j k
  · exact second_right_row18 j k
  · exact second_right_row19 j k
  · exact second_right_row20 j k
  · exact second_right_row21 j k
  · exact second_right_row22 j k
  · exact second_right_row23 j k
  · exact second_right_row24 j k
  · exact second_right_row25 j k
  · exact second_right_row26 j k
  · exact second_right_row27 j k
  · exact second_right_row28 j k
  · exact second_right_row29 j k
theorem second_accumulator_row0 (j : Fin 30) :
    (secondRecipes 0 j).accumulator 30 = outputIndices 0 j := by
  revert j
  decide
theorem second_accumulator_row1 (j : Fin 30) :
    (secondRecipes 1 j).accumulator 30 = outputIndices 1 j := by
  revert j
  decide
theorem second_accumulator_row2 (j : Fin 30) :
    (secondRecipes 2 j).accumulator 30 = outputIndices 2 j := by
  revert j
  decide
theorem second_accumulator_row3 (j : Fin 30) :
    (secondRecipes 3 j).accumulator 30 = outputIndices 3 j := by
  revert j
  decide
theorem second_accumulator_row4 (j : Fin 30) :
    (secondRecipes 4 j).accumulator 30 = outputIndices 4 j := by
  revert j
  decide
theorem second_accumulator_row5 (j : Fin 30) :
    (secondRecipes 5 j).accumulator 30 = outputIndices 5 j := by
  revert j
  decide
theorem second_accumulator_row6 (j : Fin 30) :
    (secondRecipes 6 j).accumulator 30 = outputIndices 6 j := by
  revert j
  decide
theorem second_accumulator_row7 (j : Fin 30) :
    (secondRecipes 7 j).accumulator 30 = outputIndices 7 j := by
  revert j
  decide
theorem second_accumulator_row8 (j : Fin 30) :
    (secondRecipes 8 j).accumulator 30 = outputIndices 8 j := by
  revert j
  decide
theorem second_accumulator_row9 (j : Fin 30) :
    (secondRecipes 9 j).accumulator 30 = outputIndices 9 j := by
  revert j
  decide
theorem second_accumulator_row10 (j : Fin 30) :
    (secondRecipes 10 j).accumulator 30 = outputIndices 10 j := by
  revert j
  decide
theorem second_accumulator_row11 (j : Fin 30) :
    (secondRecipes 11 j).accumulator 30 = outputIndices 11 j := by
  revert j
  decide
theorem second_accumulator_row12 (j : Fin 30) :
    (secondRecipes 12 j).accumulator 30 = outputIndices 12 j := by
  revert j
  decide
theorem second_accumulator_row13 (j : Fin 30) :
    (secondRecipes 13 j).accumulator 30 = outputIndices 13 j := by
  revert j
  decide
theorem second_accumulator_row14 (j : Fin 30) :
    (secondRecipes 14 j).accumulator 30 = outputIndices 14 j := by
  revert j
  decide
theorem second_accumulator_row15 (j : Fin 30) :
    (secondRecipes 15 j).accumulator 30 = outputIndices 15 j := by
  revert j
  decide
theorem second_accumulator_row16 (j : Fin 30) :
    (secondRecipes 16 j).accumulator 30 = outputIndices 16 j := by
  revert j
  decide
theorem second_accumulator_row17 (j : Fin 30) :
    (secondRecipes 17 j).accumulator 30 = outputIndices 17 j := by
  revert j
  decide
theorem second_accumulator_row18 (j : Fin 30) :
    (secondRecipes 18 j).accumulator 30 = outputIndices 18 j := by
  revert j
  decide
theorem second_accumulator_row19 (j : Fin 30) :
    (secondRecipes 19 j).accumulator 30 = outputIndices 19 j := by
  revert j
  decide
theorem second_accumulator_row20 (j : Fin 30) :
    (secondRecipes 20 j).accumulator 30 = outputIndices 20 j := by
  revert j
  decide
theorem second_accumulator_row21 (j : Fin 30) :
    (secondRecipes 21 j).accumulator 30 = outputIndices 21 j := by
  revert j
  decide
theorem second_accumulator_row22 (j : Fin 30) :
    (secondRecipes 22 j).accumulator 30 = outputIndices 22 j := by
  revert j
  decide
theorem second_accumulator_row23 (j : Fin 30) :
    (secondRecipes 23 j).accumulator 30 = outputIndices 23 j := by
  revert j
  decide
theorem second_accumulator_row24 (j : Fin 30) :
    (secondRecipes 24 j).accumulator 30 = outputIndices 24 j := by
  revert j
  decide
theorem second_accumulator_row25 (j : Fin 30) :
    (secondRecipes 25 j).accumulator 30 = outputIndices 25 j := by
  revert j
  decide
theorem second_accumulator_row26 (j : Fin 30) :
    (secondRecipes 26 j).accumulator 30 = outputIndices 26 j := by
  revert j
  decide
theorem second_accumulator_row27 (j : Fin 30) :
    (secondRecipes 27 j).accumulator 30 = outputIndices 27 j := by
  revert j
  decide
theorem second_accumulator_row28 (j : Fin 30) :
    (secondRecipes 28 j).accumulator 30 = outputIndices 28 j := by
  revert j
  decide
theorem second_accumulator_row29 (j : Fin 30) :
    (secondRecipes 29 j).accumulator 30 = outputIndices 29 j := by
  revert j
  decide
theorem second_accumulator (i j : Fin 30) :
    (secondRecipes i j).accumulator 30 = outputIndices i j := by
  fin_cases i
  · exact second_accumulator_row0 j
  · exact second_accumulator_row1 j
  · exact second_accumulator_row2 j
  · exact second_accumulator_row3 j
  · exact second_accumulator_row4 j
  · exact second_accumulator_row5 j
  · exact second_accumulator_row6 j
  · exact second_accumulator_row7 j
  · exact second_accumulator_row8 j
  · exact second_accumulator_row9 j
  · exact second_accumulator_row10 j
  · exact second_accumulator_row11 j
  · exact second_accumulator_row12 j
  · exact second_accumulator_row13 j
  · exact second_accumulator_row14 j
  · exact second_accumulator_row15 j
  · exact second_accumulator_row16 j
  · exact second_accumulator_row17 j
  · exact second_accumulator_row18 j
  · exact second_accumulator_row19 j
  · exact second_accumulator_row20 j
  · exact second_accumulator_row21 j
  · exact second_accumulator_row22 j
  · exact second_accumulator_row23 j
  · exact second_accumulator_row24 j
  · exact second_accumulator_row25 j
  · exact second_accumulator_row26 j
  · exact second_accumulator_row27 j
  · exact second_accumulator_row28 j
  · exact second_accumulator_row29 j
theorem second_matrix_product (values : ℕ → ℝ) :
    matrixValues (value values nodes) 30 outputIndices =
      matrixValues (value values nodes) 30 (fun i j => congruenceIndices j i) *
        matrixValues (value values nodes) 30 firstProductIndices :=
  matrix_product_recipe_sound values nodes 30 _ _ _ _ second_recipes_checked
    second_left second_right second_accumulator
theorem congruence_matrix_product (values : ℕ → ℝ) :
    matrixValues (value values nodes) 30 outputIndices =
      (matrixValues (value values nodes) 30 congruenceIndices).transpose *
        matrixValues (value values nodes) 30 hessianIndices *
          matrixValues (value values nodes) 30 congruenceIndices := by
  rw [second_matrix_product, first_matrix_product, Matrix.mul_assoc]
  rfl
#print axioms congruence_matrix_product
end ThomsonN10.Local.Certificates.AmbientKernel
