/- Adapted from global-soundness/n10/project/Thomson10Soundness/SDP/ProjectionComplex.lean (supplied accepted N10 port of proof/lean/ThomsonN9/SDP/ProjectionComplex.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, MIT). -/
import ThomsonN10.Cert.SDP.Basic
import ThomsonN10.Cert.SDP.CircleKernel

/-! Complex coordinates for the two-dimensional orthogonal complement of a unit anchor. -/

namespace ThomsonN10.Cert.SDP
open ThomsonN10 ThomsonN10.Interfaces

open scoped BigOperators

noncomputable def anchorProjection (a : R3) (ha : ‖a‖ = 1) (y : R3) :
    (ℝ ∙ a)ᗮ :=
  ⟨y - (inner ℝ a y) • a, by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    simp [inner_sub_right, real_inner_smul_right, ha]⟩

theorem anchorProjection_inner (a : R3) (ha : ‖a‖ = 1) (y w : R3) :
    inner ℝ (anchorProjection a ha y) (anchorProjection a ha w) =
      inner ℝ y w - inner ℝ a y * inner ℝ a w := by
  change inner ℝ (y - (inner ℝ a y) • a) (w - (inner ℝ a w) • a) = _
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, ha, one_pow]
  rw [real_inner_comm y a]
  ring

noncomputable def anchorPlaneEquiv (a : R3) (ha : ‖a‖ = 1) :
    (ℝ ∙ a)ᗮ ≃ₗᵢ[ℝ] ℂ := by
  letI : Fact (Module.finrank ℝ R3 = 2 + 1) := ⟨by simp [R3]⟩
  have hne : a ≠ 0 := by
    intro h
    simpa [h] using ha
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2 hne).repr.trans
    Complex.orthonormalBasisOneI.repr.symm

noncomputable def anchorComplex (a : R3) (ha : ‖a‖ = 1) (y : R3) : ℂ :=
  anchorPlaneEquiv a ha (anchorProjection a ha y)

theorem anchorComplex_mul_star_re (a : R3) (ha : ‖a‖ = 1) (y w : R3) :
    (anchorComplex a ha y * star (anchorComplex a ha w)).re =
      inner ℝ y w - inner ℝ a y * inner ℝ a w := by
  unfold anchorComplex
  rw [Complex.star_def, ← Complex.inner, (anchorPlaneEquiv a ha).inner_map_map,
    anchorProjection_inner, real_inner_comm w y]
  ring

theorem anchorComplex_normSq (a : R3) (ha : ‖a‖ = 1) (y : R3) :
    Complex.normSq (anchorComplex a ha y) = ‖y‖ ^ 2 - (inner ℝ a y) ^ 2 := by
  have h := anchorComplex_mul_star_re a ha y y
  simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    real_inner_self_eq_norm_sq, pow_two] using h

theorem anchorComplex_normSq_unit (a : R3) (ha : ‖a‖ = 1)
    (y : R3) (hy : ‖y‖ = 1) :
    Complex.normSq (anchorComplex a ha y) = 1 - (inner ℝ a y) ^ 2 := by
  rw [anchorComplex_normSq, hy, one_pow]

theorem anchorComplex_mul_star_normSq (a : R3) (ha : ‖a‖ = 1)
    (y w : R3) (hy : ‖y‖ = 1) (hw : ‖w‖ = 1) :
    Complex.normSq (anchorComplex a ha y * star (anchorComplex a ha w)) =
      (1 - (inner ℝ a y) ^ 2) * (1 - (inner ℝ a w) ^ 2) := by
  rw [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
    anchorComplex_normSq_unit a ha y hy, anchorComplex_normSq_unit a ha w hw]

theorem exists_anchorComplex (a : R3) (ha : ‖a‖ = 1) :
    ∃ z : R3 → ℂ,
      (∀ y w, (z y * star (z w)).re =
        inner ℝ y w - inner ℝ a y * inner ℝ a w) ∧
      (∀ y, Complex.normSq (z y) = ‖y‖ ^ 2 - (inner ℝ a y) ^ 2) := by
  exact ⟨anchorComplex a ha, anchorComplex_mul_star_re a ha, anchorComplex_normSq a ha⟩

noncomputable def threePointKernel (k : ℕ) (u v t : ℝ) : ℝ :=
  circleKernel (t-u*v) ((1-u^2)*(1-v^2)) k

theorem spherical_threePointKernel_nonneg {ι : Type*} [Fintype ι]
    (a : R3) (ha : ‖a‖ = 1) (x : ι → R3) (hx : ∀ i, ‖x i‖ = 1)
    (weight : ι → ℝ) (k : ℕ) :
    0 ≤ ∑ i, ∑ j, weight i * weight j *
      threePointKernel k (inner ℝ a (x i)) (inner ℝ a (x j))
        (inner ℝ (x i) (x j)) := by
  have h := circleKernel_gram_nonneg (fun i => anchorComplex a ha (x i)) weight k
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [threePointKernel, anchorComplex_mul_star_re,
    anchorComplex_mul_star_normSq a ha (x i) (x j) (hx i) (hx j)]

theorem anchored_spherical_kernel_sum_nonneg {ι : Type*} [Fintype ι]
    (x : ι → R3) (hx : ∀ i, ‖x i‖ = 1) (weight : ι → ι → ℝ) (k : ℕ) :
    0 ≤ ∑ a, ∑ i, ∑ j, weight a i * weight a j *
      threePointKernel k (inner ℝ (x a) (x i)) (inner ℝ (x a) (x j))
        (inner ℝ (x i) (x j)) := by
  exact Finset.sum_nonneg fun a _ =>
    spherical_threePointKernel_nonneg (x a) (hx a) x hx (weight a) k

#print axioms anchorComplex_mul_star_re
#print axioms anchorComplex_normSq
#print axioms anchorComplex_mul_star_normSq
#print axioms exists_anchorComplex
#print axioms spherical_threePointKernel_nonneg
#print axioms anchored_spherical_kernel_sum_nonneg

end ThomsonN10.Cert.SDP
