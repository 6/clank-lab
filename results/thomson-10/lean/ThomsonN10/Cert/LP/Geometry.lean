/- Adapted from targets/thomson-10/lp-formal/n10/Thomson10/Geometry.lean (supplied accepted N10 LP proof). N9 design: aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, proof/lean/ThomsonN9/LP/Concrete.lean. -/
import ThomsonN10.Cert.LP.Data

open scoped BigOperators
open scoped InnerProductSpace
noncomputable section
namespace ThomsonN10.Cert.LP

theorem coordDot_eq_inner (x y : Point) : coordDot x y = ⟪x,y⟫_ℝ := by
  simp [coordDot, PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]

theorem coordSq_eq_norm (x : Point) : coordSq x = ‖x‖^2 := by
  simpa [coordSq, Fin.sum_univ_succ, add_assoc] using (EuclideanSpace.real_norm_sq_eq x).symm

theorem kernel_identity (x y : Point) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    h ⟪x,y⟫_ℝ = a0 + ∑ m : Fin 24, weights m * feature m x * feature m y := by
  rw [harmonic_identity, coordDot_eq_inner, coordSq_eq_norm, coordSq_eq_norm, hx, hy]
  simpa using legendre_identity ⟪x,y⟫_ℝ

theorem inner_bounds (x y : Point) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    -1 ≤ ⟪x,y⟫_ℝ ∧ ⟪x,y⟫_ℝ ≤ 1 := by
  have hb := abs_real_inner_le_norm x y
  rw [hx,hy,one_mul] at hb
  exact abs_le.mp hb

theorem distance_sq (x y : Point) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    ‖x-y‖^2 = 2-2*⟪x,y⟫_ℝ := by
  rw [norm_sub_sq_real, hx, hy]
  ring

end ThomsonN10.Cert.LP
