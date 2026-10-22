/- Adapted from proof/lean/ThomsonN9/LocalEnergy.lean,
   aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Data
import ThomsonN10.Local.LocalGeometry
import ThomsonN10.Local.LocalPotential

namespace ThomsonN10.Local

noncomputable def coulombForce (x : Configuration) (i : Fin 10) : R3 :=
  ∑ j, (‖x i-x j‖)⁻¹^3 • (x j-x i)


noncomputable def radialCoefficient (x : Configuration) (i : Fin 10) : ℝ :=
  -(∑ j, (‖x i-x j‖)⁻¹)/2

theorem coulombForce_inner_self (x : Configuration) (hx : ∀ i, ‖x i‖ = 1)
    (i : Fin 10) : inner ℝ (x i) (coulombForce x i) = radialCoefficient x i := by
  have hpair (j : Fin 10) : (‖x i-x j‖)⁻¹^3 * inner ℝ (x i) (x j-x i) =
      -(‖x i-x j‖)⁻¹/2 := by
    have h := unit_displacement_inner (hx i) (hx j)
    rw [norm_sub_rev (x j) (x i)] at h
    rw [h]
    by_cases hd : ‖x i-x j‖ = 0
    · simp [hd]
    · field_simp
  simp only [coulombForce, inner_sum, real_inner_smul_right, hpair, radialCoefficient]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem pair_weighted_force_identity (p b : Configuration) (w : Fin 10 → Fin 10 → ℝ)
    (hw : ∀ i j, w i j = w j i) :
    pairSum (fun i j => w i j * inner ℝ (p j-p i) (b i-b j)) =
      ∑ i, inner ℝ (∑ j, w i j • (p j-p i)) (b i) := by
  let A : Fin 10 → Fin 10 → ℝ := fun i j => w i j * inner ℝ (p j-p i) (b i)
  have hij (i j : Fin 10) : w i j * inner ℝ (p j-p i) (b i-b j) = A i j+A j i := by
    dsimp [A]
    rw [inner_sub_right, hw j i]
    have heq : p i-p j = -(p j-p i) := by abel
    rw [heq, inner_neg_left]
    ring
  have hsym (i j : Fin 10) :
      w i j * inner ℝ (p j-p i) (b i-b j) =
        w j i * inner ℝ (p i-p j) (b j-b i) := by
    rw [hij i j, hij j i, add_comm]
  have ht := twice_pairSum (fun i j => w i j * inner ℝ (p j-p i) (b i-b j))
    hsym (fun i => by simp)
  simp_rw [hij] at ht
  have hswap : (∑ i, ∑ j, A j i) = ∑ i, ∑ j, A i j := Finset.sum_comm
  simp only [Finset.sum_add_distrib, hswap] at ht
  have hforce : (∑ i, inner ℝ (∑ j, w i j • (p j-p i)) (b i)) =
      ∑ i, ∑ j, A i j := by
    simp only [sum_inner, real_inner_smul_left, A]
  rw [hforce]
  simp_rw [hij]
  linarith

theorem pair_linear_coulomb_identity (p b : Configuration) :
    pairSum (fun i j => -(inner ℝ (p i-p j) (b i-b j))/‖p i-p j‖^3) =
      ∑ i, inner ℝ (coulombForce p i) (b i) := by
  have h := pair_weighted_force_identity p b (fun i j => (‖p i-p j‖)⁻¹^3)
    (fun i j => by rw [norm_sub_rev])
  have hterm (i j : Fin 10) : (‖p i-p j‖)⁻¹^3 * inner ℝ (p j-p i) (b i-b j) =
      -(inner ℝ (p i-p j) (b i-b j))/‖p i-p j‖^3 := by
    have heq : p j-p i = -(p i-p j) := by abel
    rw [heq, inner_neg_left]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  simpa only [hterm, coulombForce] using h

theorem stationary_linear_sphere_correction (p x : Configuration)
    (hp : ∀ i, ‖p i‖ = 1) (hx : ∀ i, ‖x i‖ = 1)
    (hstationary : ∀ i, coulombForce p i = radialCoefficient p i • p i) :
    pairSum (fun i j =>
      -(inner ℝ (p i-p j) ((x i-p i)-(x j-p j)))/‖p i-p j‖^3) =
        -(∑ i, radialCoefficient p i * ‖x i-p i‖^2)/2 := by
  rw [pair_linear_coulomb_identity]
  simp_rw [hstationary, real_inner_smul_left, unit_displacement_inner (hp _) (hx _)]
  calc
    (∑ i, radialCoefficient p i*(-‖x i-p i‖^2/2)) =
        ∑ i, -(radialCoefficient p i*‖x i-p i‖^2)/2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem local_gap_of_quartic_bound {rho gap : ℝ} (hr : 0 ≤ rho)
    (hr1 : rho ≤ 1/500)
    (hgap : 7/100*rho^2-(2477/100)*rho^3-(1107/400)*rho^4 ≤ gap) :
    rho^2/50 ≤ gap := by
  have hr2 : rho^2 ≤ (1/500 : ℝ)^2 := by nlinarith
  have hc : (1/50 : ℝ) ≤ 7/100-(2477/100)*rho-(1107/400)*rho^2 := by
    nlinarith [algebraic_local_constants]
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg rho)
  nlinarith

end ThomsonN10.Local
