import PostLie.Jacobi
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Algebra.Algebra.Rat

namespace PostLie

open Polynomial

variable {k I : Type*} [Field k] [Fintype I] [DecidableEq I]

/-- A fixed truncation of the exponential of `t A`, with polynomial matrix entries. -/
noncomputable def expMatrix (A : Matrix I I k) (r : ℕ) : Matrix I I k[X] :=
  ∑ j ∈ Finset.range r, (C ((j.factorial : k)⁻¹) * X ^ j) • (A ^ j).map C

@[simp] lemma expMatrix_apply (A : Matrix I I k) (r : ℕ) (i l : I) :
    expMatrix A r i l =
      ∑ j ∈ Finset.range r, C ((j.factorial : k)⁻¹ * (A ^ j) i l) * X ^ j := by
  simp [expMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- Evaluation of the polynomial exponential at a scalar parameter. -/
lemma eval_expMatrix (A : Matrix I I k) (r : ℕ) (t : k) :
    (expMatrix A r).map (Polynomial.evalRingHom t) =
      ∑ j ∈ Finset.range r, ((j.factorial : k)⁻¹ * t ^ j) • A ^ j := by
  apply Matrix.ext
  intro i l
  simp [expMatrix_apply, Matrix.sum_apply, Matrix.smul_apply, Polynomial.eval_finsetSum,
    mul_left_comm, mul_comm]

/-- The initial value of every positive truncation is the identity matrix. -/
lemma eval_zero_expMatrix (A : Matrix I I k) (r : ℕ) :
    (expMatrix A (r + 1)).map (Polynomial.evalRingHom 0) = 1 := by
  rw [eval_expMatrix, Finset.sum_range_succ']
  simp

variable [CharZero k]

/-- Differentiation removes the first exponential coefficient and shifts the powers of `A`. -/
lemma derivative_expMatrix_apply (A : Matrix I I k) (r : ℕ) (i l : I) :
    (expMatrix A (r + 1) i l).derivative =
      ∑ j ∈ Finset.range r, C ((j.factorial : k)⁻¹ * (A ^ (j + 1)) i l) * X ^ j := by
  rw [expMatrix_apply, Finset.sum_range_succ']
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
    derivative_add, derivative_C, add_zero, map_sum, derivative_C_mul_X_pow]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  congr 2
  field_simp

/-- The truncated exponential solves the matrix differential equation once the final power
of `A` is zero. -/
theorem derivative_expMatrix (A : Matrix I I k) (r : ℕ) (h : A ^ (r + 1) = 0) :
    (expMatrix A (r + 1)).map derivative = A.map C * expMatrix A (r + 1) := by
  have hm : A.map C * expMatrix A (r + 1) =
      ∑ j ∈ Finset.range (r + 1),
        (C ((j.factorial : k)⁻¹) * X ^ j) • (A ^ (j + 1)).map C := by
    simp only [expMatrix, Matrix.mul_sum, Matrix.mul_smul, ← Matrix.map_mul, ← pow_succ']
  rw [hm, Finset.sum_range_succ, h]
  apply Matrix.ext
  intro i l
  rw [Matrix.map_apply, derivative_expMatrix_apply]
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.map_apply, Matrix.zero_apply, map_zero, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]
  ring

/-- The polynomial exponential evaluates to Mathlib's finite nilpotent exponential. -/
lemma eval_expMatrix_eq_exp (A : Matrix I I k) (r : ℕ)
    (h : A ^ r = 0) (t : k) :
    (expMatrix A r).map (Polynomial.evalRingHom t) = IsNilpotent.exp (t • A) := by
  have ht : (t • A) ^ r = 0 := by rw [smul_pow, h, smul_zero]
  rw [eval_expMatrix, IsNilpotent.exp_eq_sum ht]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_pow]
  apply Matrix.ext
  intro i l
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hq : ((j.factorial : ℚ)⁻¹) • (t ^ j * (A ^ j) i l) =
      ((j.factorial : k)⁻¹) * (t ^ j * (A ^ j) i l) := by
    simpa [smul_eq_mul] using
      ratCast_smul_eq ℚ k ((j.factorial : ℚ)⁻¹) (t ^ j * (A ^ j) i l)
  rw [hq, mul_assoc]

variable {J H : Type*} [Fintype J] [DecidableEq J] [Fintype H]

omit [Fintype I] [DecidableEq I] [CharZero k] [DecidableEq J] [Fintype H] in
/-- Entrywise differentiation obeys the matrix product rule. -/
lemma derivative_matrix_mul (A : Matrix I J k[X]) (B : Matrix J H k[X]) :
    (A * B).map derivative = A.map derivative * B + A * B.map derivative := by
  apply Matrix.ext
  intro i h
  simp [Matrix.mul_apply, derivative_mul, Finset.sum_add_distrib]

omit [Fintype I] [DecidableEq I] [CharZero k] [Fintype J] [DecidableEq J] in
@[simp] lemma derivative_constant_matrix (A : Matrix I J k) :
    (A.map C).map derivative = 0 := by
  apply Matrix.ext
  intro i j
  simp

/-- The projected exponential, expressed as a polynomial matrix. -/
noncomputable def matrixFlow (U : Matrix I J k) (A : Matrix J J k)
    (V : Matrix J H k) (r : ℕ) : Matrix I H k[X] :=
  U.map C * expMatrix A r * V.map C

omit [Fintype I] [DecidableEq I] [CharZero k] [Fintype H] in
lemma eval_matrixFlow (U : Matrix I J k) (A : Matrix J J k)
    (V : Matrix J H k) (r : ℕ) (t : k) :
    (matrixFlow U A V r).map (evalRingHom t) =
      U * (expMatrix A r).map (evalRingHom t) * V := by
  unfold matrixFlow
  rw [Matrix.map_mul, Matrix.map_mul]
  have hc (a : k) : evalRingHom t (C a) = a := eval_C
  simp only [Matrix.map_map, Function.comp_def, hc]
  rfl

omit [Fintype I] [DecidableEq I] [Fintype H] in
lemma derivative_matrixFlow (U : Matrix I J k) (A : Matrix J J k)
    (V : Matrix J H k) (r : ℕ) (hr : A ^ (r + 1) = 0) :
    (matrixFlow U A V (r + 1)).map derivative =
      U.map C * A.map C * expMatrix A (r + 1) * V.map C := by
  classical
  simp only [matrixFlow, derivative_matrix_mul, derivative_constant_matrix,
    Matrix.zero_mul, add_zero, Matrix.mul_zero, zero_add, derivative_expMatrix A r hr]
  simp only [Matrix.mul_assoc]

omit [Fintype I] [DecidableEq I] [CharZero k] [Fintype J] [DecidableEq J] in
@[simp] lemma eval_constant_matrix (U : Matrix I J k) (t : k) :
    (U.map C).map (evalRingHom t) = U := by
  apply Matrix.ext
  intro i j
  simp

omit [Fintype I] [DecidableEq I] [Fintype H] in
lemma eval_derivative_matrixFlow (U : Matrix I J k) (A : Matrix J J k)
    (V : Matrix J H k) (r : ℕ) (hr : A ^ (r + 1) = 0) (t : k) :
    ((matrixFlow U A V (r + 1)).map derivative).map (evalRingHom t) =
      U * A * (expMatrix A (r + 1)).map (evalRingHom t) * V := by
  classical
  rw [derivative_matrixFlow U A V r hr]
  simp only [Matrix.map_mul, eval_constant_matrix]

/-- Changing coordinates commutes with the finite exponential. -/
lemma toLin_eval_expMatrix {V : Type*} [AddCommGroup V] [Module k V] [Module ℚ V]
    (b : Module.Basis I k V) (A : Matrix I I k) (r : ℕ)
    (h : A ^ r = 0) (t : k) :
    Matrix.toLin b b ((expMatrix A r).map (evalRingHom t)) =
      IsNilpotent.exp (t • Matrix.toLin b b A) := by
  rw [eval_expMatrix_eq_exp A r h]
  have ht : IsNilpotent (t • A) := ⟨r, by rw [smul_pow, h, smul_zero]⟩
  change (Matrix.toLinAlgEquiv b) (IsNilpotent.exp (t • A)) = _
  rw [ht.map_exp (Matrix.toLinAlgEquiv b), map_smul]
  rfl

end PostLie
