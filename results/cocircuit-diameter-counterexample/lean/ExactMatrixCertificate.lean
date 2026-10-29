import PerturbedStar

namespace ADKZPricing
open Matrix
noncomputable section

/-- A rational right inverse is a finite arithmetic certificate for an
    integer minor, without expanding its permutation determinant. -/
theorem integer_det_ne_zero_of_rational_right_inverse {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) (B : Matrix (Fin r) (Fin r) ℚ)
    (h : A.map (Int.castRingHom ℚ) * B = 1) : A.det ≠ 0 := by
  have he := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at he
  have hc := Int.cast_det (R := ℚ) A
  change (A.det : ℚ) = (A.map (Int.castRingHom ℚ)).det at hc
  intro hz
  rw [← hc, hz] at he
  norm_num at he

#print axioms integer_det_ne_zero_of_rational_right_inverse
end
end ADKZPricing
