/- Adapted from proof/ambient_circuit/export_lean_bounds.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelAll
import ThomsonN10.Local.Certificates.AmbientCongruence
import ThomsonN10.Local.Certificates.CircuitCoordinates
import ThomsonN10.Local.Certificates.ZeroPenalty
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
def OutputIntegerCheck (s : ℤ) (a : ScaledInterval) (i j : Fin 30) : Prop :=
  if i = j then s ≤ 1000*a.lo ∧ a.hi ≤ 100*s
  else -s ≤ 100000*a.lo ∧ 100000*a.hi ≤ s
instance instDecidableOutputIntegerCheck (s : ℤ) (a : ScaledInterval) (i j : Fin 30) :
    Decidable (OutputIntegerCheck s a i j) := by unfold OutputIntegerCheck; infer_instance
theorem outputIntegerCheck_sound {s : ℤ} {a : ScaledInterval} {i j : Fin 30}
    (hs : 0 < s) (h : OutputIntegerCheck s a i j) :
    OutputWithin s a (zeroPenaltyCongruenceBounds i j) := by
  have hsQ : (0 : ℚ) < (s : ℚ) := by exact_mod_cast hs
  unfold OutputIntegerCheck at h
  unfold OutputWithin ScaledInterval.rational zeroPenaltyCongruenceBounds
  by_cases hij : i = j
  · simp only [hij, if_true] at h ⊢
    constructor
    · rw [le_div_iff₀ hsQ]
      have hh : (s : ℚ) ≤ 1000*(a.lo : ℚ) := by exact_mod_cast h.1
      linarith
    · rw [div_le_iff₀ hsQ]
      exact_mod_cast h.2
  · simp only [hij, if_false] at h ⊢
    constructor
    · rw [le_div_iff₀ hsQ]
      have hh : -(s : ℚ) ≤ 100000*(a.lo : ℚ) := by exact_mod_cast h.1
      linarith
    · rw [div_le_iff₀ hsQ]
      have hh : 100000*(a.hi : ℚ) ≤ (s : ℚ) := by exact_mod_cast h.2
      linarith
theorem scale_positive : 0 < scale := by decide
theorem parameter_inputs_enclosed (r : CandidateParameter) :
    ∀ i, ScaledInterval.Contains scale (inputs i) (parameterInputs r i) := by
  intro i
  by_cases hi : i = 0
  · subst i
    change (647766592527497741273099129797364779105989678357359219 : ℝ) ≤
      (scale : ℝ)*(r : ℝ) ∧ (scale : ℝ)*(r : ℝ) ≤
        (647766592527497741273099129797364779105989678357359220 : ℝ)
    have hs : (0 : ℝ) ≤ (scale : ℝ) := by exact_mod_cast le_of_lt scale_positive
    constructor
    · calc
        _ ≤ (scale : ℝ)*(heightLower : ℝ) := by norm_num [scale,heightLower]
        _ ≤ _ := mul_le_mul_of_nonneg_left r.property.1 hs
    · calc
        _ ≤ (scale : ℝ)*(heightUpper : ℝ) := mul_le_mul_of_nonneg_left r.property.2.1 hs
        _ ≤ _ := by norm_num [scale,heightUpper]
  · simp [ScaledInterval.Contains,inputs,parameterInputs,hi]
theorem output_bounds_0 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 0 j)).bound
      (zeroPenaltyCongruenceBounds 0 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_0 (j : Fin 30) :
    outputIndices 0 j < 45592 := by revert j; decide
theorem output_bounds_1 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 1 j)).bound
      (zeroPenaltyCongruenceBounds 1 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_1 (j : Fin 30) :
    outputIndices 1 j < 45592 := by revert j; decide
theorem output_bounds_2 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 2 j)).bound
      (zeroPenaltyCongruenceBounds 2 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_2 (j : Fin 30) :
    outputIndices 2 j < 45592 := by revert j; decide
theorem output_bounds_3 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 3 j)).bound
      (zeroPenaltyCongruenceBounds 3 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_3 (j : Fin 30) :
    outputIndices 3 j < 45592 := by revert j; decide
theorem output_bounds_4 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 4 j)).bound
      (zeroPenaltyCongruenceBounds 4 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_4 (j : Fin 30) :
    outputIndices 4 j < 45592 := by revert j; decide
theorem output_bounds_5 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 5 j)).bound
      (zeroPenaltyCongruenceBounds 5 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_5 (j : Fin 30) :
    outputIndices 5 j < 45592 := by revert j; decide
theorem output_bounds_6 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 6 j)).bound
      (zeroPenaltyCongruenceBounds 6 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_6 (j : Fin 30) :
    outputIndices 6 j < 45592 := by revert j; decide
theorem output_bounds_7 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 7 j)).bound
      (zeroPenaltyCongruenceBounds 7 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_7 (j : Fin 30) :
    outputIndices 7 j < 45592 := by revert j; decide
theorem output_bounds_8 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 8 j)).bound
      (zeroPenaltyCongruenceBounds 8 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_8 (j : Fin 30) :
    outputIndices 8 j < 45592 := by revert j; decide
theorem output_bounds_9 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 9 j)).bound
      (zeroPenaltyCongruenceBounds 9 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_9 (j : Fin 30) :
    outputIndices 9 j < 45592 := by revert j; decide
theorem output_bounds_10 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 10 j)).bound
      (zeroPenaltyCongruenceBounds 10 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_10 (j : Fin 30) :
    outputIndices 10 j < 45592 := by revert j; decide
theorem output_bounds_11 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 11 j)).bound
      (zeroPenaltyCongruenceBounds 11 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_11 (j : Fin 30) :
    outputIndices 11 j < 45592 := by revert j; decide
theorem output_bounds_12 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 12 j)).bound
      (zeroPenaltyCongruenceBounds 12 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_12 (j : Fin 30) :
    outputIndices 12 j < 45592 := by revert j; decide
theorem output_bounds_13 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 13 j)).bound
      (zeroPenaltyCongruenceBounds 13 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_13 (j : Fin 30) :
    outputIndices 13 j < 45592 := by revert j; decide
theorem output_bounds_14 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 14 j)).bound
      (zeroPenaltyCongruenceBounds 14 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_14 (j : Fin 30) :
    outputIndices 14 j < 45592 := by revert j; decide
theorem output_bounds_15 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 15 j)).bound
      (zeroPenaltyCongruenceBounds 15 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_15 (j : Fin 30) :
    outputIndices 15 j < 45592 := by revert j; decide
theorem output_bounds_16 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 16 j)).bound
      (zeroPenaltyCongruenceBounds 16 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_16 (j : Fin 30) :
    outputIndices 16 j < 45592 := by revert j; decide
theorem output_bounds_17 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 17 j)).bound
      (zeroPenaltyCongruenceBounds 17 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_17 (j : Fin 30) :
    outputIndices 17 j < 45592 := by revert j; decide
theorem output_bounds_18 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 18 j)).bound
      (zeroPenaltyCongruenceBounds 18 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_18 (j : Fin 30) :
    outputIndices 18 j < 45592 := by revert j; decide
theorem output_bounds_19 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 19 j)).bound
      (zeroPenaltyCongruenceBounds 19 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_19 (j : Fin 30) :
    outputIndices 19 j < 45592 := by revert j; decide
theorem output_bounds_20 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 20 j)).bound
      (zeroPenaltyCongruenceBounds 20 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_20 (j : Fin 30) :
    outputIndices 20 j < 45592 := by revert j; decide
theorem output_bounds_21 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 21 j)).bound
      (zeroPenaltyCongruenceBounds 21 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_21 (j : Fin 30) :
    outputIndices 21 j < 45592 := by revert j; decide
theorem output_bounds_22 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 22 j)).bound
      (zeroPenaltyCongruenceBounds 22 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_22 (j : Fin 30) :
    outputIndices 22 j < 45592 := by revert j; decide
theorem output_bounds_23 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 23 j)).bound
      (zeroPenaltyCongruenceBounds 23 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_23 (j : Fin 30) :
    outputIndices 23 j < 45592 := by revert j; decide
theorem output_bounds_24 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 24 j)).bound
      (zeroPenaltyCongruenceBounds 24 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_24 (j : Fin 30) :
    outputIndices 24 j < 45592 := by revert j; decide
theorem output_bounds_25 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 25 j)).bound
      (zeroPenaltyCongruenceBounds 25 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_25 (j : Fin 30) :
    outputIndices 25 j < 45592 := by revert j; decide
theorem output_bounds_26 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 26 j)).bound
      (zeroPenaltyCongruenceBounds 26 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_26 (j : Fin 30) :
    outputIndices 26 j < 45592 := by revert j; decide
theorem output_bounds_27 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 27 j)).bound
      (zeroPenaltyCongruenceBounds 27 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_27 (j : Fin 30) :
    outputIndices 27 j < 45592 := by revert j; decide
theorem output_bounds_28 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 28 j)).bound
      (zeroPenaltyCongruenceBounds 28 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_28 (j : Fin 30) :
    outputIndices 28 j < 45592 := by revert j; decide
theorem output_bounds_29 (j : Fin 30) :
    OutputWithin scale (nodes (outputIndices 29 j)).bound
      (zeroPenaltyCongruenceBounds 29 j) := by
  apply outputIntegerCheck_sound scale_positive
  revert j
  decide
theorem output_index_29 (j : Fin 30) :
    outputIndices 29 j < 45592 := by revert j; decide
theorem output_bounds (i j : Fin 30) :
    OutputWithin scale (nodes (outputIndices i j)).bound
      (zeroPenaltyCongruenceBounds i j) := by
  fin_cases i
  · exact output_bounds_0 j
  · exact output_bounds_1 j
  · exact output_bounds_2 j
  · exact output_bounds_3 j
  · exact output_bounds_4 j
  · exact output_bounds_5 j
  · exact output_bounds_6 j
  · exact output_bounds_7 j
  · exact output_bounds_8 j
  · exact output_bounds_9 j
  · exact output_bounds_10 j
  · exact output_bounds_11 j
  · exact output_bounds_12 j
  · exact output_bounds_13 j
  · exact output_bounds_14 j
  · exact output_bounds_15 j
  · exact output_bounds_16 j
  · exact output_bounds_17 j
  · exact output_bounds_18 j
  · exact output_bounds_19 j
  · exact output_bounds_20 j
  · exact output_bounds_21 j
  · exact output_bounds_22 j
  · exact output_bounds_23 j
  · exact output_bounds_24 j
  · exact output_bounds_25 j
  · exact output_bounds_26 j
  · exact output_bounds_27 j
  · exact output_bounds_28 j
  · exact output_bounds_29 j
theorem output_index (i j : Fin 30) : outputIndices i j < 45592 := by
  fin_cases i
  · exact output_index_0 j
  · exact output_index_1 j
  · exact output_index_2 j
  · exact output_index_3 j
  · exact output_index_4 j
  · exact output_index_5 j
  · exact output_index_6 j
  · exact output_index_7 j
  · exact output_index_8 j
  · exact output_index_9 j
  · exact output_index_10 j
  · exact output_index_11 j
  · exact output_index_12 j
  · exact output_index_13 j
  · exact output_index_14 j
  · exact output_index_15 j
  · exact output_index_16 j
  · exact output_index_17 j
  · exact output_index_18 j
  · exact output_index_19 j
  · exact output_index_20 j
  · exact output_index_21 j
  · exact output_index_22 j
  · exact output_index_23 j
  · exact output_index_24 j
  · exact output_index_25 j
  · exact output_index_26 j
  · exact output_index_27 j
  · exact output_index_28 j
  · exact output_index_29 j
theorem congruence_upper_checked : ∀ i j : Fin 30, j < i →
    ZeroAt nodes (congruenceIndices i j) := by decide
theorem congruence_diagonal_checked : ∀ i : Fin 30,
    OneAt nodes (congruenceIndices i i) := by decide
theorem output_enclosures (r : CandidateParameter) (i j : Fin 30) :
    (zeroPenaltyCongruenceBounds i j).Contains
      (value (parameterInputs r) nodes (outputIndices i j)) :=
  outputWithin_sound scale_positive
    (all_enclosures _ (parameter_inputs_enclosed r) _ (output_index i j)) (output_bounds i j)
theorem flattened_posDef (r : CandidateParameter)
    (hA : (matrixValues (value (parameterInputs r) nodes) 30 hessianIndices).IsHermitian) :
    (matrixValues (value (parameterInputs r) nodes) 30 hessianIndices).PosDef := by
  let C := matrixValues (value (parameterInputs r) nodes) 30 congruenceIndices
  have hupper : ∀ i j, j < i → C i j = 0 := by
    intro i j hij
    exact zeroAt_sound _ nodes _ (congruence_upper_checked i j hij)
  have hdiag : ∀ i, C i i = 1 := by
    intro i
    exact oneAt_sound _ nodes _ (congruence_diagonal_checked i)
  apply zeroPenalty_posDef_of_congruence_enclosures _ C hA hupper hdiag
  intro i j
  have hstar : star C = C.transpose := by ext a b; simp
  rw [hstar]
  change (zeroPenaltyCongruenceBounds i j).Contains
    (((matrixValues (value (parameterInputs r) nodes) 30 congruenceIndices).transpose *
      matrixValues (value (parameterInputs r) nodes) 30 hessianIndices *
        matrixValues (value (parameterInputs r) nodes) 30 congruenceIndices) i j)
  rw [← congruence_matrix_product]
  exact output_enclosures r i j
#print axioms outputIntegerCheck_sound
#print axioms parameter_inputs_enclosed
#print axioms output_enclosures
#print axioms flattened_posDef
end ThomsonN10.Local.Certificates.AmbientKernel
