/- Adapted from proof/lean/ThomsonN9/LocalGeometry.lean,
   aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.CentroidBound

/-! Geometric estimates used by the quantitative local argument. -/

namespace ThomsonN10.Local

theorem unit_displacement_inner {p x : R3} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) :
    inner ℝ p (x-p) = -‖x-p‖^2/2 := by
  have h := norm_sub_sq_real x p
  rw [hp, hx, ← real_inner_comm x p] at h
  rw [inner_sub_right, real_inner_self_eq_norm_sq, hp]
  nlinarith

noncomputable def tangentDisplacement (p b : R3) : R3 := b+(‖b‖^2/2) • p

theorem tangentDisplacement_inner {p b : R3} (hp : ‖p‖ = 1)
    (hb : inner ℝ p b = -‖b‖^2/2) :
    inner ℝ p (tangentDisplacement p b) = 0 := by
  simp only [tangentDisplacement, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hp, hb]
  ring

theorem tangentDisplacement_norm_sq {p b : R3} (hp : ‖p‖ = 1)
    (hb : inner ℝ p b = -‖b‖^2/2) :
    ‖tangentDisplacement p b‖^2 = ‖b‖^2-‖b‖^4/4 := by
  rw [tangentDisplacement, norm_add_sq_real, real_inner_smul_right,
    ← real_inner_comm b p, hb, norm_smul, hp]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖b‖^2/2)]
  ring

theorem tangentDisplacement_preserves_perp {p b v : R3}
    (hv : inner ℝ p v = 0) :
    inner ℝ (tangentDisplacement p b) v = inner ℝ b v := by
  simp [tangentDisplacement, inner_add_left, real_inner_smul_left, hv]

theorem tangentDisplacement_error_sq {p b : R3} (hp : ‖p‖ = 1) :
    ‖b-tangentDisplacement p b‖^2 = ‖b‖^4/4 := by
  have heq : b-tangentDisplacement p b = -(‖b‖^2/2) • p := by
    unfold tangentDisplacement
    module
  rw [heq, norm_smul, hp, Real.norm_eq_abs, mul_one, sq_abs]
  ring

theorem displacement_pair_squared_sum (b : Configuration) :
    pairSum (fun i j => ‖b i-b j‖^2) =
      10*(∑ i, ‖b i‖^2)-‖∑ i, b i‖^2 := by
  have ht := twice_pairSum (fun i j => ‖b i-b j‖^2)
    (fun i j => by rw [norm_sub_rev]) (fun i => by simp)
  have hs : (∑ i, ∑ j, ‖b i-b j‖^2) =
      20*(∑ i, ‖b i‖^2)-2*‖∑ i, b i‖^2 := by
    simp_rw [norm_sub_sq_real]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← inner_sum, ← sum_inner, real_inner_self_eq_norm_sq, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  linarith

theorem displacement_pair_norm_bound (b : Configuration) {rho : ℝ}
    (hr : 0 ≤ rho) (hs : ∑ i, ‖b i‖^2 = rho^2)
    {i j : Fin 10} (hij : i ≠ j) : ‖b i-b j‖ ≤ (3/2 : ℝ)*rho := by
  classical
  have htwo : ‖b i‖^2+‖b j‖^2 ≤ rho^2 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({i,j} : Finset (Fin 10)) ⊆ Finset.univ from Finset.subset_univ _)
      (fun k _ _ => sq_nonneg ‖b k‖)
    simpa [hij, hs] using h
  have hn := sq_nonneg ‖b i+b j‖
  rw [norm_add_sq_real] at hn
  have hd := norm_sub_sq_real (b i) (b j)
  nlinarith [norm_nonneg (b i-b j)]

theorem displacement_pair_cubic_sum (b : Configuration) {rho : ℝ}
    (hr : 0 ≤ rho) (hs : ∑ i, ‖b i‖^2 = rho^2) :
    pairSum (fun i j => ‖b i-b j‖^3) ≤ (15 : ℝ)*rho^3 := by
  have ht : pairSum (fun i j => ‖b i-b j‖^3) ≤
      (3/2 : ℝ)*rho*pairSum (fun i j => ‖b i-b j‖^2) := by
    unfold pairSum
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j hj
    have h := mul_le_mul_of_nonneg_right
      (displacement_pair_norm_bound b hr hs (Finset.mem_Ioi.mp hj).ne)
      (sq_nonneg ‖b i-b j‖)
    nlinarith
  rw [displacement_pair_squared_sum, hs] at ht
  have hn := mul_nonneg (show 0 ≤ (3/2 : ℝ)*rho by positivity)
    (sq_nonneg ‖∑ i, b i‖)
  nlinarith

theorem displacement_fourth_sum (b : Configuration) {rho : ℝ}
    (hs : ∑ i, ‖b i‖^2 = rho^2) : ∑ i, ‖b i‖^4 ≤ rho^4 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => ‖b i‖^2) (fun i _ => sq_nonneg ‖b i‖)
  simpa only [← pow_mul, hs] using h

end ThomsonN10.Local
