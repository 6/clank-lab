import PostLie.Cocycle
import PostLie.Jacobi
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace PostLie

open Polynomial

variable {k g n I : Type*} [Field k] [CharZero k]
  [LieRing g] [LieAlgebra k g] [LieRing n] [LieAlgebra k n]
  [FiniteDimensional k g] [FiniteDimensional k n] [LieRing.IsNilpotent n]
  [Fintype I] [DecidableEq I]

/-- A polynomial family of cocycles satisfying the translation equation has constant
determinant. It suffices to use the trace identity at its invertible scalar values. -/
theorem det_constant_of_cocycle_flow
    (L : g →ₗ⁅k⁆ LieDerivation k n n) (e : g ≃ₗ[k] n) (b : Module.Basis I k n)
    (M : Matrix I I k[X]) (z : n)
    (hC : ∀ t : k, IsCocycle L
      ((Matrix.toLin b b (M.map (evalRingHom t))).comp e.toLinearMap))
    (hV : ∀ t : k,
      (Matrix.toLin b b ((M.map derivative).map (evalRingHom t))).comp e.toLinearMap =
        velocity L ((Matrix.toLin b b (M.map (evalRingHom t))).comp e.toLinearMap) z)
    (htrace : ∀ a, LinearMap.trace k n (L a).toLinearMap =
      LinearMap.trace k g (LieAlgebra.ad k g a)) :
    M.det = C (M.det.eval 0) := by
  apply det_constant_of_trace_inverse
  intro t ht
  let A := M.map (evalRingHom t)
  let B := (M.map derivative).map (evalRingHom t)
  let Q : n ≃ₗ[k] n := Matrix.toLinearEquiv b A (isUnit_iff_ne_zero.mpr ht)
  let P : g ≃ₗ[k] n := e.trans Q
  have hP : P.toLinearMap = (Matrix.toLin b b A).comp e.toLinearMap := rfl
  have hPQ : P.symm.toLinearMap = e.symm.toLinearMap.comp Q.symm.toLinearMap := rfl
  have hv : Matrix.toLin b b B =
      (velocity L P.toLinearMap z).comp e.symm.toLinearMap := by
    apply LinearMap.ext
    intro w
    have hh := LinearMap.congr_fun (hV t) (e.symm w)
    change (Matrix.toLin b b B) (e (e.symm w)) =
      velocity L P.toLinearMap z (e.symm w) at hh
    simpa only [LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe] using hh
  have hh := trace_velocity_of_cocycle L P (by simpa only [hP] using hC t) htrace z
  have heq : (A⁻¹ * B).trace =
      LinearMap.trace k n (Q.symm.toLinearMap.comp (Matrix.toLin b b B)) := by
    rw [LinearMap.trace_eq_matrix_trace k b, LinearMap.toMatrix_comp b b b]
    change (A⁻¹ * B).trace =
      (LinearMap.toMatrix b b (Matrix.toLin b b A⁻¹) *
        LinearMap.toMatrix b b (Matrix.toLin b b B)).trace
    simp
  change (A⁻¹ * B).trace = 0
  rw [heq, LinearMap.trace_comp_comm', hv, LinearMap.comp_assoc, ← hPQ]
  exact hh

end PostLie
