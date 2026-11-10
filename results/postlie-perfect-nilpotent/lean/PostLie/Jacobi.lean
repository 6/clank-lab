import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace PostLie

open Polynomial

variable {k I : Type*} [Fintype I] [DecidableEq I]

section Ring

variable [CommRing k]

/-- The derivative of a determinant is the sum of its column derivatives. -/
theorem derivative_det_columns (M : Matrix I I k[X]) :
    M.det.derivative =
      ∑ j, (M.updateCol j (fun i => (M i j).derivative)).det := by
  classical
  simp only [Matrix.det_apply', map_sum, derivative_mul, derivative_intCast,
    zero_mul, zero_add, derivative_prod_finset, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  rw [mul_comm]
  have heq : (fun i => M.updateCol j (fun i => (M i j).derivative) (σ i) i) =
      Function.update (fun i => M (σ i) i) j ((M (σ j) j).derivative) := by
    funext i
    by_cases hi : i = j <;> simp [hi]
  rw [heq, Finset.prod_update_of_mem (Finset.mem_univ j)]
  rw [Finset.sdiff_singleton_eq_erase]

/-- Jacobi's formula for a matrix with polynomial entries, without an invertibility assumption. -/
theorem derivative_det (M : Matrix I I k[X]) :
    M.det.derivative = (M.adjugate * M.map derivative).trace := by
  rw [derivative_det_columns]
  simp only [Matrix.trace]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

end Ring

section Field

variable [Field k] [CharZero k]

/-- A polynomial is constant if its derivative vanishes away from its zero set. -/
lemma polynomial_constant_of_derivative_off_zeros (f : k[X])
    (h : ∀ t : k, f.eval t ≠ 0 → f.derivative.eval t = 0) :
    f = C (f.eval 0) := by
  have hp : f * f.derivative = 0 := by
    apply Polynomial.funext
    intro t
    by_cases ht : f.eval t = 0 <;> simp [ht, h t]
  by_cases hf : f = 0
  · simp [hf]
  · have hd := (mul_eq_zero.mp hp).resolve_left hf
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using
      Polynomial.eq_C_of_derivative_eq_zero hd

omit [CharZero k] in
/-- Jacobi's formula after evaluation at a scalar parameter. -/
lemma eval_derivative_det (M : Matrix I I k[X]) (t : k) :
    M.det.derivative.eval t =
      ((M.map (Polynomial.evalRingHom t)).adjugate *
        (M.map derivative).map (Polynomial.evalRingHom t)).trace := by
  rw [derivative_det]
  change Polynomial.evalRingHom t _ = _
  rw [AddMonoidHom.map_trace, Matrix.map_mul]
  have ha : M.adjugate.map (Polynomial.evalRingHom t) =
      (M.map (Polynomial.evalRingHom t)).adjugate :=
    (Polynomial.evalRingHom t).map_adjugate M
  rw [ha]

/-- The determinant is constant if the evaluated Jacobi trace vanishes at every invertible value.
The conclusion does not require any assumption at singular parameter values. -/
theorem det_constant_of_trace_adjugate (M : Matrix I I k[X])
    (htrace : ∀ t : k, (M.map (Polynomial.evalRingHom t)).det ≠ 0 →
      ((M.map (Polynomial.evalRingHom t)).adjugate *
        (M.map derivative).map (Polynomial.evalRingHom t)).trace = 0) :
    M.det = C (M.det.eval 0) := by
  apply polynomial_constant_of_derivative_off_zeros
  intro t ht
  rw [eval_derivative_det]
  apply htrace t
  have he := (Polynomial.evalRingHom t).map_det M
  change M.det.eval t = (M.map (Polynomial.evalRingHom t)).det at he
  rw [← he]
  exact ht

/-- A polynomial matrix has constant determinant when its logarithmic derivative is traceless
at every parameter value where it is invertible. -/
theorem det_constant_of_trace_inverse (M : Matrix I I k[X])
    (htrace : ∀ t : k, (M.map (Polynomial.evalRingHom t)).det ≠ 0 →
      ((M.map (Polynomial.evalRingHom t))⁻¹ *
        (M.map derivative).map (Polynomial.evalRingHom t)).trace = 0) :
    M.det = C (M.det.eval 0) := by
  apply det_constant_of_trace_adjugate
  intro t ht
  have h := htrace t ht
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mul, Matrix.trace_smul] at h
  exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero ht)

end Field

end PostLie
