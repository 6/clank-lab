/- Adapted from global-soundness/n10/project/Thomson10Soundness/SDP/GeometryBounds.lean (supplied accepted N10 port of proof/lean/ThomsonN9/SDP/GeometryBounds.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, MIT). -/
import ThomsonN10.Cert.SDP.ProjectionComplex
import ThomsonN10.Cert.SDP.Basic

namespace ThomsonN10.Cert.SDP
open ThomsonN10 ThomsonN10.Interfaces

theorem unit_inner_abs_le_one (x y : R3) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |inner ℝ x y| ≤ 1 := by simpa [hx, hy] using abs_real_inner_le_norm x y

theorem unit_triple_gram_nonneg (x y z : R3)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    0 ≤ 1+2*(inner ℝ x y)*(inner ℝ x z)*(inner ℝ y z)-
      (inner ℝ x y)^2-(inner ℝ x z)^2-(inner ℝ y z)^2 := by
  let w := anchorComplex x hx y*star (anchorComplex x hx z)
  have hre : w.re = inner ℝ y z-inner ℝ x y*inner ℝ x z :=
    anchorComplex_mul_star_re x hx y z
  have hn : Complex.normSq w = (1-(inner ℝ x y)^2)*(1-(inner ℝ x z)^2) :=
    anchorComplex_mul_star_normSq x hx y z hy hz
  have h : w.re^2 ≤ Complex.normSq w := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg w.im]
  rw [hre, hn] at h
  nlinarith

theorem distinct_inner_lt_one {x : Configuration} (hx : IsSphereConfiguration x)
    {i j : Fin 10} (hij : i ≠ j) : inner ℝ (x i) (x j) < 1 := by
  have hp := pair_distance_pos hx hij
  have hd := norm_sub_sq_real (x i) (x j)
  rw [hx.1 i, hx.1 j] at hd
  nlinarith [sq_pos_of_pos hp]

noncomputable def coulombPotential (t : ℝ) : ℝ := (Real.sqrt (2-2*t))⁻¹

theorem pair_energy_eq_potential (x y : R3) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (‖x-y‖)⁻¹ = coulombPotential (inner ℝ x y) := by
  have hd : ‖x-y‖^2 = 2-2*inner ℝ x y := by
    rw [norm_sub_sq_real, hx, hy]
    ring
  unfold coulombPotential
  rw [← hd, Real.sqrt_sq (norm_nonneg _)]

end ThomsonN10.Cert.SDP
