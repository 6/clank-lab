import StanleySmithForms.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Ring

/-!
# The witness at `λ = (5,2)`, `k = 7`: the weak remark fails

`A52` is the matrix of the Jucys–Murphy element
`X₇ = (1 7) + (2 7) + ⋯ + (6 7)` on the Specht module `S^(5,2)`, in the standard
polytabloid basis (the 14 standard Young tableaux of shape `(5,2)`, in the order
of the certificate), with column `j` holding the coordinates of the image of
basis vector `j`. This file checks the matrix computation only:

* unimodular `U52`, `V52` bring `A52` to `diag(1,1,1,1,2,4,4,4,4,0,0,0,0,0)`;
* `A52 (A52 - 4) = 0`, and the eigenvalues of `A52` over `ℚ` are exactly `0`
  and `4`;
* every diagonalization of `A52` by unimodular matrices has an entry divisible
  by `2` but not by `4`, which is not a product of the eigenvalues `0` and `4`.
-/

namespace StanleySmithForms

open Matrix

/-- The matrix of `X₇` on `S^(5,2)` in the standard polytabloid basis. -/
def A52 : Matrix (Fin 14) (Fin 14) ℤ :=
  !![ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      1,  1,  4,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      1,  0,  0,  1,  4,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  1,  0,  1,  0,  4,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      1,  0,  0,  0,  0,  0,  1,  4,  0,  0,  0,  0,  0,  0;
      0,  1,  0,  0,  0,  0,  1,  0,  4,  0,  0,  0,  0,  0;
      0,  0,  0,  1,  0,  0,  1,  0,  0,  4,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
     -3,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  4,  0,  0;
      1, -2,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  4,  0;
      1,  1,  0, -1,  0,  0,  0,  0,  0,  0,  1,  0,  0,  4]

/-- The left transformation matrix. -/
def U52 : Matrix (Fin 14) (Fin 14) ℤ :=
  !![ 0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  1,  0, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  1,  0,  0, -1,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  3,  0,  0,  0,  1,  0,  0;
      0,  0, -1,  0, -1,  1,  0,  2,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0, -1,  1,  0,  1, -1,  0,  0,  0,  0,  0;
      0,  0, -1,  0,  1,  0,  0,  0,  1, -1,  0,  0,  0,  0;
      0,  0,  1,  0,  0,  0,  0,  3, -3,  0,  0,  1, -1,  0;
      0,  0,  0,  0,  0,  0,  0,  4, -5,  1,  0,  1, -2,  1;
      0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0;
      0,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0]

/-- The right transformation matrix. -/
def V52 : Matrix (Fin 14) (Fin 14) ℤ :=
  !![  1,  -1,  -1,   0,  -1,   2,   0,  -2,   0,  -4,   4,   2,  -2,   0;
       0,   1,   1,   0,   1,  -2,   0,  -2,   0,  -8,   8,   2,  -2,   0;
       0,   0,   0,   0,   0,   0,   0,   1,   0,   3,  -3,  -1,   1,   0;
       0,   0,   1,   0,   1,  -2,  -4,  -2,  -4, -24,  24,   6, -10,   4;
       0,   0,   0,   0,   0,   0,   1,   1,   1,   7,  -7,  -2,   3,  -1;
       0,   0,   0,   0,   0,   1,   1,   1,   1,   8,  -8,  -2,   3,  -1;
       0,   0,   0,   0,   1,  -2,   0,   2,   0,   4,  -8,  -2,   2,   0;
       0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   1,   0,   0,   0;
       0,   0,   0,   0,   0,   0,   0,   0,   0,   1,   0,   0,   0,   0;
       0,   0,   0,   0,   0,   0,   0,   0,   1,   5,  -4,  -1,   2,  -1;
       0,   0,   0,   1,  -3,   6,   0,  -6,   0, -12,  12,   2,  -6,   0;
       0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   1,   0,   0;
       0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   1,   0;
       0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   1]

/-- An integer inverse of `U52`. -/
def U52inv : Matrix (Fin 14) (Fin 14) ℤ :=
  !![ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1;
      1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0;
      1, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  1,  2,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0;
      1, -1, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  1,  1,  0,  1, -1,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  1,  0,  1, -1, -1,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0;
     -3,  3,  3,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      1, -3, -3,  1, -3,  3,  0, -1,  0,  0,  0,  0,  0,  0;
      1,  0, -1,  1, -2,  2,  1, -2,  1,  0,  0,  0,  0,  0]

/-- An integer inverse of `V52`. -/
def V52inv : Matrix (Fin 14) (Fin 14) ℤ :=
  !![ 1,  1,  4,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  1,  4, -1, -4,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  1,  4,  0, -1, -4,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  3, 12,  0,  0,  1,  4,  0,  0;
      0,  0, -2,  0, -2,  2,  1,  4,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0, -1,  1,  0,  1, -1,  0,  0,  0,  0,  0;
      0,  0, -1,  0,  1,  0,  0,  0,  1, -1,  0,  0,  0,  0;
      0,  0,  1,  0,  0,  0,  0,  3, -3,  0,  0,  1, -1,  0;
      0,  0,  0,  0,  0,  0,  0,  4, -5,  1,  0,  1, -2,  1;
      0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1]

set_option maxRecDepth 100000

theorem U52_mul_U52inv : U52 * U52inv = 1 := by decide +kernel

theorem V52_mul_V52inv : V52 * V52inv = 1 := by decide +kernel

theorem U52_unimodular : IsUnit U52.det := isUnit_det_of_right_inverse U52_mul_U52inv

theorem V52_unimodular : IsUnit V52.det := isUnit_det_of_right_inverse V52_mul_V52inv

/-- The Smith normal form of `A52`. -/
theorem smith_form_52 :
    U52 * A52 * V52 = Matrix.diagonal ![1, 1, 1, 1, 2, 4, 4, 4, 4, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- `A52` satisfies `x (x - 4) = 0`. -/
theorem eigen_identity_52 : A52 * (A52 - 4 • 1) = 0 := by decide +kernel

theorem A52_mul_self : A52 * A52 = (4 : ℤ) • A52 := by decide +kernel

/-- `A52` is lower triangular. -/
theorem A52_transpose_isUpperTriangular : A52ᵀ.IsUpperTriangular := by
  have h : ∀ i j : Fin 14, j < i → A52 j i = 0 := by decide +kernel
  exact fun i j hij => h i j hij

/-- The characteristic polynomial of `A52`. -/
theorem charpoly_52 : A52.charpoly = Polynomial.X ^ 5 * (Polynomial.X - 4) ^ 9 := by
  rw [← charpoly_transpose, charpoly_of_isUpperTriangular _ A52_transpose_isUpperTriangular]
  simp [Fin.prod_univ_succ, A52]
  ring

/-- An eigenvector for `0`. -/
def v0 : Fin 14 → ℤ := ![-4, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, -3, 1, 1]

/-- An eigenvector for `4`. -/
def v4 : Fin 14 → ℤ := ![0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, -3, 1, 1]

theorem A52_mulVec_v0 : A52 *ᵥ v0 = 0 := by decide +kernel

theorem A52_mulVec_v4 : A52 *ᵥ v4 = 4 • v4 := by decide +kernel

/-- The eigenvalues of `A52` over `ℚ` are exactly `0` and `4`. -/
theorem eigenvalues_52 : ∀ μ : ℚ,
    (∃ v : Fin 14 → ℚ, v ≠ 0 ∧ (A52.map (Int.cast : ℤ → ℚ)) *ᵥ v = μ • v) ↔
      (μ = 0 ∨ μ = 4) := by
  intro μ
  set M : Matrix (Fin 14) (Fin 14) ℚ := A52.map (Int.cast : ℤ → ℚ) with hMdef
  have cast_mulVec : ∀ u : Fin 14 → ℤ,
      M *ᵥ (fun i => (u i : ℚ)) = fun i => ((A52 *ᵥ u) i : ℚ) := fun u => by
    ext i
    exact (RingHom.map_mulVec (Int.castRingHom ℚ) A52 u i).symm
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hM : M * M = (4 : ℚ) • M := by
      ext i j
      have h := congrFun (congrFun A52_mul_self i) j
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h
      simp only [M, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      exact_mod_cast h
    have h2 : (μ * (μ - 4)) • v = 0 := by
      have h := congrArg (fun N => N *ᵥ v) hM
      simp only [← mulVec_mulVec, smul_mulVec, hv, mulVec_smul] at h
      rw [mul_sub, sub_smul, ← smul_smul, ← smul_smul, h, smul_comm μ (4 : ℚ) v, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.1 h)
    · exact absurd h hv0
  · rintro (rfl | rfl)
    · refine ⟨fun i => (v0 i : ℚ), fun h => ?_, ?_⟩
      · have := congrFun h 0
        simp [v0] at this
      · rw [cast_mulVec, A52_mulVec_v0, zero_smul]
        rfl
    · refine ⟨fun i => (v4 i : ℚ), fun h => ?_, ?_⟩
      · have := congrFun h 2
        simp [v4] at this
      · rw [cast_mulVec, A52_mulVec_v4]
        ext i
        simp

/-- A parity certificate for an entry exactly divisible by `2`: if
`A y = 2 x`, `w A = 2 z` and `w ⬝ x` is odd, then every diagonalization of `A`
by unimodular matrices has an entry divisible by `2` but not by `4`. -/
theorem exists_two_exact_of_certificate {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℤ} {x y w z : n → ℤ} (hy : A *ᵥ y = 2 • x) (hw : w ᵥ* A = 2 • z)
    (hwx : ¬ 2 ∣ w ⬝ᵥ x) {P Q : Matrix n n ℤ} (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    {d : n → ℤ} (hd : P * A * Q = Matrix.diagonal d) :
    ∃ i, 2 ∣ d i ∧ ¬ 4 ∣ d i := by
  set x' := P *ᵥ x
  set y' := Q⁻¹ *ᵥ y
  set w' := w ᵥ* P⁻¹
  have h1 : ∀ i, d i * y' i = 2 * x' i := by
    have : Matrix.diagonal d *ᵥ y' = 2 • x' := by
      rw [← hd, mulVec_mulVec, Matrix.mul_assoc (P * A), mul_nonsing_inv _ hQ, Matrix.mul_one,
        ← mulVec_mulVec, hy, mulVec_smul]
    intro i
    have := congrFun this i
    rwa [mulVec_diagonal] at this
  have h2 : ∀ i, w' i * d i = 2 * (z ᵥ* Q) i := by
    have : w' ᵥ* Matrix.diagonal d = 2 • (z ᵥ* Q) := by
      rw [← hd, vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hP,
        Matrix.one_mul, ← vecMul_vecMul, hw, smul_vecMul]
    intro i
    have := congrFun this i
    rwa [vecMul_diagonal] at this
  have h3 : w' ⬝ᵥ x' = w ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_vecMul, nonsing_inv_mul _ hP, vecMul_one]
  by_contra hall
  push Not at hall
  apply hwx
  rw [← h3]
  refine Finset.dvd_sum fun i _ => ?_
  by_cases hwi : (2 : ℤ) ∣ w' i
  · exact dvd_mul_of_dvd_left hwi _
  · have hdi : (2 : ℤ) ∣ d i := by
      rcases Int.even_mul.1 (even_iff_two_dvd.2 ⟨_, h2 i⟩) with h | h
      · exact absurd (even_iff_two_dvd.1 h) hwi
      · exact even_iff_two_dvd.1 h
    have h4 : (4 : ℤ) ∣ 2 * x' i := by
      rw [← h1 i]; exact dvd_mul_of_dvd_left (hall i hdi) _
    exact dvd_mul_of_dvd_right (by omega) _

/-- The certificate vectors for `A52`, read off from `U52` and `V52` at the entry
`2` of the Smith form. -/
def x52 : Fin 14 → ℤ := ![0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, -3, -2]
def y52 : Fin 14 → ℤ := ![-1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -3, 0, 0, 0]
def w52 : Fin 14 → ℤ := ![0, 0, -1, 0, -1, 1, 0, 2, 0, 0, 0, 0, 0, 0]
def z52 : Fin 14 → ℤ := ![0, 0, -2, 0, -2, 2, 1, 4, 0, 0, 0, 0, 0, 0]

theorem A52_mulVec_y52 : A52 *ᵥ y52 = 2 • x52 := by decide +kernel

theorem w52_vecMul_A52 : w52 ᵥ* A52 = 2 • z52 := by decide +kernel

theorem w52_dotProduct_x52 : w52 ⬝ᵥ x52 = 1 := by decide +kernel

/-- Every diagonalization of `A52` by unimodular matrices has an entry divisible
by `2` but not by `4`. -/
theorem weak_remark_fails_52 : ∀ P Q : Matrix (Fin 14) (Fin 14) ℤ,
    IsUnit P.det → IsUnit Q.det → ∀ d, P * A52 * Q = Matrix.diagonal d →
      ∃ i, 2 ∣ d i ∧ ¬ 4 ∣ d i := fun _ _ hP hQ _ hd =>
  exists_two_exact_of_certificate A52_mulVec_y52 w52_vecMul_A52
    (by rw [w52_dotProduct_x52]; decide) hP hQ hd

/-- The counterexample at `λ = (5,2)`, `k = 7` to the weak form of Stanley's
remark (every invariant factor is a product of eigenvalues).

Lean checks the matrix computation only: unimodular `U52`, `V52` bring `A52` to
its Smith form `diag(1,1,1,1,2,4,4,4,4,0,0,0,0,0)`; the eigenvalues of `A52`
over `ℚ` are exactly `0` and `4`; and every unimodular diagonalization of `A52`
has an entry divisible by `2` but not by `4`, which is no product of `0`s and
`4`s. It does not check that `A52` is the matrix of `X₇` on the Specht module
`S^(5,2)` in the standard polytabloid basis; the certificate checkers do. -/
theorem counterexample_52 :
    (IsUnit U52.det ∧ IsUnit V52.det ∧
      U52 * A52 * V52 = Matrix.diagonal ![1, 1, 1, 1, 2, 4, 4, 4, 4, 0, 0, 0, 0, 0]) ∧
    (∀ μ : ℚ, (∃ v : Fin 14 → ℚ, v ≠ 0 ∧ (A52.map (Int.cast : ℤ → ℚ)) *ᵥ v = μ • v) ↔
      (μ = 0 ∨ μ = 4)) ∧
    (∀ P Q : Matrix (Fin 14) (Fin 14) ℤ, IsUnit P.det → IsUnit Q.det →
      ∀ d, P * A52 * Q = Matrix.diagonal d → ∃ i, 2 ∣ d i ∧ ¬ 4 ∣ d i) :=
  ⟨⟨U52_unimodular, V52_unimodular, smith_form_52⟩, eigenvalues_52, weak_remark_fails_52⟩

end StanleySmithForms
