import RationalNormalization

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- The weights are divided by the SAME positive denominator that scales
    all matrix entries. Their second common denominator clears all cells
    at once, keeping a single chart T e₀ and the original row labels. -/
def adjustedWeights {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℚ)
    (w : Option (Fin n) → Fin n → ℚ) : Option (Fin n) × Fin n → ℚ :=
  fun p => w p.1 p.2 / matrixDenominator A

def integralChartScale {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℚ)
    (w : Option (Fin n) → Fin n → ℚ) : ℕ := commonDenominator (adjustedWeights A w)

def integralChartWeights {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℚ)
    (w : Option (Fin n) → Fin n → ℚ) (c : Option (Fin n)) (i : Fin n) : ℤ :=
  integralNumerator (adjustedWeights A w) (c, i)

theorem integralChartWeights_positive {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ) (w : Option (Fin n) → Fin n → ℚ)
    (hw : ∀ c i, 0 < w c i) (c : Option (Fin n)) (i : Fin n) :
    0 < integralChartWeights A w c i := by
  have hS : (0 : ℚ) < matrixDenominator A := by
    exact_mod_cast (integralMatrix_positive_scaling A).1
  have hT : (0 : ℚ) < integralChartScale A w := by
    exact_mod_cast commonDenominator_positive (adjustedWeights A w)
  have hv : (integralChartWeights A w c i : ℚ) =
      (integralChartScale A w : ℚ) * (w c i / matrixDenominator A) :=
    integralNumerator_value _ _
  have hp : (0 : ℚ) < integralChartWeights A w c i := by
    rw [hv]
    exact mul_pos hT (div_pos (hw c i) hS)
  exact_mod_cast hp

theorem integralChartWeights_representation {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ) (w : Option (Fin n) → Fin n → ℚ)
    (hr : ∀ c j, (if j = 0 then 1 else 0 : ℚ) = ∑ i, w c i * starSign c i * A i j)
    (c : Option (Fin n)) (j : Fin (d + 1)) :
    (if j = 0 then (integralChartScale A w : ℤ) else 0) =
      ∑ i, integralChartWeights A w c i * (starSign c i * integralMatrix A i j) := by
  have hS : (matrixDenominator A : ℚ) ≠ 0 := by
    exact_mod_cast (integralMatrix_positive_scaling A).1.ne'
  have hv (i : Fin n) : (integralChartWeights A w c i : ℚ) =
      (integralChartScale A w : ℚ) * (w c i / matrixDenominator A) :=
    integralNumerator_value _ _
  have hs (i : Fin n) : ((starSign c i : ℤ) : ℚ) = starSign c i := by
    unfold starSign
    split_ifs <;> norm_num
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
  push_cast
  simp only [hv, hs, integralMatrix_value]
  have he : (∑ i, (integralChartScale A w : ℚ) * (w c i / matrixDenominator A) *
      (starSign c i * ((matrixDenominator A : ℚ) * A i j))) =
      (integralChartScale A w : ℚ) * ∑ i, w c i * starSign c i * A i j := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    field_simp
    ring
  rw [he, ← hr c j]
  split_ifs <;> simp

theorem integralMatrix_minor_nonzero {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (f : Fin r → Fin n) (hf : (A.submatrix f id).det ≠ 0) :
    ((integralMatrix A).submatrix f id).det ≠ 0 := by
  have hS : (matrixDenominator A : ℚ) ≠ 0 := by
    exact_mod_cast (commonDenominator_positive (fun p : Fin n × Fin r => A p.1 p.2)).ne'
  have he : (((integralMatrix A).submatrix f id).map (Int.castRingHom ℚ)) =
      (matrixDenominator A : ℚ) • A.submatrix f id := by
    ext i j
    exact integralMatrix_value A (f i) j
  have hd : ((((integralMatrix A).submatrix f id).det : ℤ) : ℚ) ≠ 0 := by
    rw [Int.cast_det]
    change ((((integralMatrix A).submatrix f id).map (Int.castRingHom ℚ))).det ≠ 0
    rw [he, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hS) hf
  exact fun hz => hd (by rw [hz]; simp)

/-- No regularity or stability property is assumed here: the finite rational
    chart representations and one nonzero minor are converted exactly. -/
def normalizedIntegralStarChart {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ) (w : Option (Fin n) → Fin n → ℚ)
    (hw : ∀ c i, 0 < w c i)
    (hr : ∀ c j, (if j = 0 then 1 else 0 : ℚ) = ∑ i, w c i * starSign c i * A i j)
    (f : Fin (d + 1) → Fin n) (hinj : Function.Injective f)
    (hf : (A.submatrix f id).det ≠ 0) : IntegralStarChart (integralMatrix A) where
  chart := fun j => if j = 0 then (integralChartScale A w : ℤ) else 0
  weights := integralChartWeights A w
  positive := integralChartWeights_positive A w hw
  representation := integralChartWeights_representation A w hr
  basis := f
  basis_injective := hinj
  basis_det := integralMatrix_minor_nonzero A f hf

#print axioms normalizedIntegralStarChart
end
end ADKZPricing
