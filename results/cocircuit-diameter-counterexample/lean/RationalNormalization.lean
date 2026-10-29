import ProductChartWeights

namespace ADKZPricing
open Matrix Finset
noncomputable section

def commonDenominator {I : Type*} [Fintype I] (q : I → ℚ) : ℕ := ∏ i, (q i).den

def integralNumerator {I : Type*} [Fintype I] (q : I → ℚ) (i : I) : ℤ :=
  (q i).num * (commonDenominator q / (q i).den : ℕ)

theorem commonDenominator_positive {I : Type*} [Fintype I] (q : I → ℚ) :
    0 < commonDenominator q := Finset.prod_pos (fun i _ => (q i).den_pos)

/-- One exact denominator clearing applies to the entire finite family.
    It is an explicit integer expression and need not be expanded to decimal. -/
theorem integralNumerator_value {I : Type*} [Fintype I] (q : I → ℚ) (i : I) :
    (integralNumerator q i : ℚ) = (commonDenominator q : ℚ) * q i := by
  classical
  have hd : (q i).den ∣ commonDenominator q := Finset.dvd_prod_of_mem _ (mem_univ i)
  have hf : ((commonDenominator q / (q i).den : ℕ) : ℚ) * ((q i).den : ℚ) =
      (commonDenominator q : ℚ) := by exact_mod_cast Nat.div_mul_cancel hd
  have hden : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_nz
  simp only [integralNumerator, Int.cast_mul, Int.cast_natCast]
  conv_rhs => rw [← (q i).num_div_den]
  rw [← mul_div_assoc]
  apply (eq_div_iff hden).mpr
  rw [mul_assoc, hf, mul_comm]

def integralMatrix {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ) : Matrix (Fin n) (Fin r) ℤ :=
  fun i j => integralNumerator (fun p : Fin n × Fin r => A p.1 p.2) (i, j)

def matrixDenominator {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ) : ℕ :=
  commonDenominator (fun p : Fin n × Fin r => A p.1 p.2)

theorem integralMatrix_value {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ) (i : Fin n) (j : Fin r) :
    (integralMatrix A i j : ℚ) = (matrixDenominator A : ℚ) * A i j :=
  integralNumerator_value _ (i, j)

theorem integralMatrix_positive_scaling {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℚ) :
    0 < matrixDenominator A ∧
    ((integralMatrix A).map (Int.castRingHom ℚ)) = rowScaled A (fun _ => (matrixDenominator A : ℚ)) := by
  refine ⟨commonDenominator_positive _, ?_⟩
  ext i j
  exact integralMatrix_value A i j

/-- Uniformity/strict cells and all original zero labels can therefore be
    transported through this SAME positive scaling, including all81cells. -/
theorem integralMatrix_star_iff {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℚ)
    (c : Option (Fin n)) (v : Fin (d + 1) → ℚ) :
    StarFeasible ((integralMatrix A).map (Int.castRingHom ℚ)) c v ↔ StarFeasible A c v := by
  rw [(integralMatrix_positive_scaling A).2]
  apply rowScaled_star_iff
  intro i
  exact_mod_cast (integralMatrix_positive_scaling A).1

#print axioms integralNumerator_value
#print axioms integralMatrix_star_iff
end
end ADKZPricing
