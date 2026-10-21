import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Algebra.Field.ZMod

/-!
# The witness for Stanley's Conjecture 7.4 at `λ = (3,1,1)`, `k = 3`

`A` is the matrix of the Jucys–Murphy element `X₃ = (1 3) + (2 3)` acting on the
Specht module `S^(3,1,1)`, in the standard polytabloid basis
`123/4/5, 124/3/5, 125/3/4, 134/2/5, 135/2/4, 145/2/3`: column `j` holds the
coordinates of the image of basis vector `j`. This file checks the matrix
computation only: `U * A * V` is the diagonal matrix `diag(1,1,1,1,2,2)` for
unimodular `U` and `V`, while the conjectured form `diag(1,1,1,1,1,4)` is not
reachable from `A` by unimodular row and column operations.
-/

namespace StanleySmithForms

open Matrix

/-- The matrix of `X₃` on `S^(3,1,1)` in the standard polytabloid basis. -/
def A : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 2,  0,  0,  0,  0,  0;
     -1, -1,  0,  0,  0,  0;
      1,  0, -1,  0,  0,  0;
      0,  1,  0,  1,  0,  0;
      0,  0,  1,  0,  1,  0;
      0,  0,  0, -1, -1, -2]

/-- The left transformation matrix. -/
def U : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 0, -1,  0,  0,  0,  0;
      0, -1, -1,  0,  0,  0;
      0, -1, -1, -1,  0,  0;
      0,  1,  1,  1,  1,  0;
     -1,  0,  2,  0,  2,  0;
      0, -1, -1, -1, -1, -1]

/-- The right transformation matrix. -/
def V : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 1, -1,  1,  1, -1,  0;
      0,  1, -1, -1,  1,  0;
      0,  0,  1,  1, -1,  0;
      0,  0,  0,  1, -1,  0;
      0,  0,  0,  0,  1,  0;
      0,  0,  0,  0,  0,  1]

/-- `U` is unimodular. -/
theorem U_det : U.det = -1 := by
  simp [U, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

/-- `V` is unimodular. -/
theorem V_det : V.det = 1 := by
  simp [V, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

/-- The determinant of `A`. Both `diag(1,1,1,1,2,2)` and the conjectured
`diag(1,1,1,1,1,4)` have determinant `4`, so the determinant alone does not
separate them. -/
theorem A_det : A.det = -4 := by
  simp [A, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem U_isUnit_det : IsUnit U.det := by
  rw [U_det]; exact isUnit_one.neg

theorem V_isUnit_det : IsUnit V.det := by
  rw [V_det]; exact isUnit_one

/-- The Smith normal form of `A`. -/
theorem smith_form : U * A * V = Matrix.diagonal ![1, 1, 1, 1, 2, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U, A, V, Matrix.mul_apply, Fin.sum_univ_succ]

/-- `2 A⁻¹`, an integer matrix. -/
def B : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 1,  0,  0,  0,  0,  0;
     -1, -2,  0,  0,  0,  0;
      1,  0, -2,  0,  0,  0;
      1,  2,  0,  2,  0,  0;
     -1,  0,  2,  0,  2,  0;
      0, -1, -1, -1, -1, -1]

/-- `A B = 2`, so every invariant factor of `A` divides `2`. -/
theorem A_mul_B : A * B = 2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A, B, Matrix.mul_apply, Fin.sum_univ_succ]

/-- `B A = 2`. -/
theorem B_mul_A : B * A = 2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A, B, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Reduction modulo two, entrywise. -/
abbrev modTwo (M : Matrix (Fin 6) (Fin 6) ℤ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  M.map (Int.castRingHom (ZMod 2))

/-- A unimodular integer matrix stays invertible modulo two. -/
theorem isUnit_det_modTwo {P : Matrix (Fin 6) (Fin 6) ℤ} (hP : IsUnit P.det) :
    IsUnit (modTwo P).det := by
  have h := hP.map (Int.castRingHom (ZMod 2))
  rwa [RingHom.map_det] at h

/-- Multiplying by unimodular matrices on both sides does not change the rank
modulo two. -/
theorem rank_modTwo_mul {P M Q : Matrix (Fin 6) (Fin 6) ℤ}
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    (modTwo (P * M * Q)).rank = (modTwo M).rank := by
  rw [modTwo, Matrix.map_mul, Matrix.map_mul,
    rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_modTwo hQ),
    rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_modTwo hP)]

/-- The rank modulo two of an integer diagonal matrix is the number of odd
diagonal entries. -/
theorem rank_modTwo_diagonal (d : Fin 6 → ℤ) :
    (modTwo (Matrix.diagonal d)).rank =
      Fintype.card {i // (d i : ZMod 2) ≠ 0} := by
  rw [modTwo, Matrix.diagonal_map (map_zero _)]
  exact rank_diagonal _

/-- `A` has rank `4` over `ZMod 2`, read off from its Smith form. -/
theorem rank_mod_two : (A.map (Int.castRingHom (ZMod 2))).rank = 4 := by
  have h := rank_modTwo_mul (M := A) U_isUnit_det V_isUnit_det
  rw [smith_form, rank_modTwo_diagonal] at h
  change (modTwo A).rank = 4
  rw [← h]
  decide

/-- The diagonal form predicted by Stanley's Conjecture 7.4 is not reachable from `A`
by unimodular row and column operations: its rank modulo two is `5`, not `4`. -/
theorem not_predicted :
    ¬ ∃ P Q : Matrix (Fin 6) (Fin 6) ℤ, IsUnit P.det ∧ IsUnit Q.det ∧
      P * A * Q = Matrix.diagonal ![1, 1, 1, 1, 1, 4] := by
  rintro ⟨P, Q, hP, hQ, h⟩
  have h2 := rank_modTwo_mul (M := A) hP hQ
  rw [h, rank_modTwo_diagonal] at h2
  change _ = (modTwo A).rank at h2
  rw [rank_mod_two] at h2
  revert h2
  decide

/-- The counterexample to Stanley's Conjecture 7.4 at `λ = (3,1,1)`, `k = 3`.

Lean checks the matrix computation only: unimodular `U` and `V` bring `A` to
`diag(1,1,1,1,2,2)`, and no unimodular `P`, `Q` bring it to the predicted
`diag(1,1,1,1,1,4)`. It does not check that `A` is the matrix of `X₃` on the
Specht module, i.e. the construction of `S^(3,1,1)` from its definition. -/
theorem counterexample :
    (IsUnit U.det ∧ IsUnit V.det ∧ U * A * V = Matrix.diagonal ![1, 1, 1, 1, 2, 2]) ∧
    ¬ ∃ P Q : Matrix (Fin 6) (Fin 6) ℤ, IsUnit P.det ∧ IsUnit Q.det ∧
      P * A * Q = Matrix.diagonal ![1, 1, 1, 1, 1, 4] :=
  ⟨⟨U_isUnit_det, V_isUnit_det, smith_form⟩, not_predicted⟩

end StanleySmithForms
