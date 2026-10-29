import ActiveKernel
import NormalizedRegularity

namespace ADKZPricing
open Matrix Polynomial Finset
noncomputable section

/-- Polynomial specialization is the adjugate of the SAME labelled
    specialized matrix, not an abstract kernel with unrelated coordinates. -/
theorem evaluated_adjugate_ray {n d : ℕ}
    (A D : Matrix (Fin n) (Fin (d + 1)) ℤ) (f : Fin (d + 1) → Fin n)
    (t : ℚ) (j : Fin (d + 1)) :
    ((linearMatrix (fun i k => A (f i) k) (fun i k => D (f i) k)).adjugate j 0).eval₂
      (Int.castRingHom ℚ) t = cofactorRay ((specializedMatrix A D t).submatrix f id) j := by
  let E := Polynomial.eval₂RingHom (Int.castRingHom ℚ) t
  let K := linearMatrix (fun i k => A (f i) k) (fun i k => D (f i) k)
  have hm : K.map E = (specializedMatrix A D t).submatrix f id := by
    ext i k
    change (C (A (f i) k) + X * C (D (f i) k)).eval₂ (Int.castRingHom ℚ) t = _
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rfl
  have he := E.map_adjugate K
  change K.adjugate.map E = (K.map E).adjugate at he
  rw [hm] at he
  exact congrArg (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ => M j 0) he

theorem oriented_adjugate_eval {n d : ℕ}
    (A D : Matrix (Fin n) (Fin (d + 1)) ℤ) (f : Fin (d + 1) → Fin n)
    (t : ℚ) (u : ℤˣ) (j : Fin (d + 1)) :
    (u • (linearMatrix (fun i k => A (f i) k) (fun i k => D (f i) k)).adjugate j 0).eval₂
      (Int.castRingHom ℚ) t =
      (u : ℤ) * cofactorRay ((specializedMatrix A D t).submatrix f id) j := by
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    simp [Units.smul_def, evaluated_adjugate_ray]

theorem constant_adjugate_ray {n d : ℕ}
    (A D : Matrix (Fin n) (Fin (d + 1)) ℤ) (f : Fin (d + 1) → Fin n)
    (j : Fin (d + 1)) :
    ((((linearMatrix (fun i k => A (f i) k) (fun i k => D (f i) k)).adjugate j 0).coeff 0 : ℤ) : ℚ) =
      cofactorRay ((A.map (Int.castRingHom ℚ)).submatrix f id) j := by
  rw [constant_linear_adjugate]
  have he := (Int.castRingHom ℚ).map_adjugate (A.submatrix f id)
  exact congrArg (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ => M j 0) he

theorem oriented_adjugate_constant {n d : ℕ}
    (A D : Matrix (Fin n) (Fin (d + 1)) ℤ) (f : Fin (d + 1) → Fin n)
    (u : ℤˣ) (j : Fin (d + 1)) :
    (((u • (linearMatrix (fun i k => A (f i) k) (fun i k => D (f i) k)).adjugate j 0).coeff 0 : ℤ) : ℚ) =
      (u : ℤ) * cofactorRay ((A.map (Int.castRingHom ℚ)).submatrix f id) j := by
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    simp [Units.smul_def, constant_adjugate_ray]

theorem rowPolynomial_evaluation {n r : ℕ}
    (A D : Matrix (Fin n) (Fin r) ℤ) (W : Fin r → Polynomial ℤ)
    (t : ℚ) (i : Fin n) :
    (rowPolynomial A D W i).eval₂ (Int.castRingHom ℚ) t =
      specializedMatrix A D t i ⬝ᵥ (fun j => (W j).eval₂ (Int.castRingHom ℚ) t) := by
  simp only [rowPolynomial, Polynomial.eval₂_finset_sum, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, specializedMatrix, dotProduct]
  rfl

theorem signed_rowPolynomial_evaluation {n r : ℕ}
    (A D : Matrix (Fin n) (Fin r) ℤ) (W : Fin r → Polynomial ℤ)
    (t : ℚ) (i : Fin n) (s : ℤˣ) :
    (s • rowPolynomial A D W i).eval₂ (Int.castRingHom ℚ) t =
      (s : ℤ) * (specializedMatrix A D t i ⬝ᵥ
        (fun j => (W j).eval₂ (Int.castRingHom ℚ) t)) := by
  rcases Int.units_eq_one_or s with rfl | rfl <;>
    simp [Units.smul_def, rowPolynomial_evaluation]

#print axioms evaluated_adjugate_ray
#print axioms signed_rowPolynomial_evaluation
end
end ADKZPricing
