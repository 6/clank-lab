/- Adapted from proof/lean/ThomsonN9/LocalEstimate.lean,
   aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.LocalEnergy

/-! Checked algebraic local energy estimates, using the chord displacement. -/

namespace ThomsonN10.Local

noncomputable def pairSecondVariation (p b : Configuration) (i j : Fin 10) : ℝ :=
  (3*(inner ℝ (p i-p j) (b i-b j))^2-‖p i-p j‖^2*‖b i-b j‖^2)/‖p i-p j‖^5

noncomputable def constrainedSecondVariation (p b : Configuration) : ℝ :=
  pairSum (pairSecondVariation p b)-(∑ i, radialCoefficient p i*‖b i‖^2)

theorem pair_potential_lower_unit_scale {d w : R3}
    (hd : 1 ≤ ‖d‖) (hw : ‖w‖ ≤ ‖d‖/200) :
    1/‖d‖-inner ℝ d w/‖d‖^3+
      (3*(inner ℝ d w)^2-‖d‖^2*‖w‖^2)/(2*‖d‖^5)-
      (51/50 : ℝ)*‖w‖^3 ≤ 1/‖d+w‖ := by
  have h := pair_potential_algebraic_lower (by linarith : 0 < ‖d‖) hw
  have hr := div_le_self (by positivity : 0 ≤ ‖w‖^3) (one_le_pow₀ hd : 1 ≤ ‖d‖^4)
  rw [mul_div_assoc] at h
  linarith

theorem energy_gap_lower_algebraic (p x : Configuration) {rho : ℝ}
    (hp : ∀ i, ‖p i‖ = 1) (hx : ∀ i, ‖x i‖ = 1)
    (hstationary : ∀ i, coulombForce p i = radialCoefficient p i • p i)
    (hdistance : ∀ i j, i < j → 1 ≤ ‖p i-p j‖)
    (hr : 0 ≤ rho) (hr1 : rho ≤ 1/500)
    (hs : ∑ i, ‖x i-p i‖^2 = rho^2) :
    constrainedSecondVariation p (fun i => x i-p i)/2-(153/10)*rho^3 ≤
      coulombEnergy x-coulombEnergy p := by
  let b : Configuration := fun i => x i-p i
  have hb : ∑ i, ‖b i‖^2 = rho^2 := hs
  have hpair (i j : Fin 10) (hij : i < j) :
      (‖p i-p j‖)⁻¹+(-(inner ℝ (p i-p j) (b i-b j))/‖p i-p j‖^3)+
        pairSecondVariation p b i j/2-(51/50)*‖b i-b j‖^3 ≤ (‖x i-x j‖)⁻¹ := by
    have hw := displacement_pair_norm_bound b hr hb hij.ne
    have hdist := hdistance i j hij
    have hwsmall : ‖b i-b j‖ ≤ ‖p i-p j‖/200 := by linarith
    have h := pair_potential_lower_unit_scale hdist hwsmall
    have heq : (p i-p j)+(b i-b j) = x i-x j := by dsimp [b]; abel
    rw [heq] at h
    convert h using 1 <;> simp only [pairSecondVariation, one_div, div_eq_mul_inv, mul_inv] <;> ring
  have hsum : pairSum (fun i j =>
      (‖p i-p j‖)⁻¹+(-(inner ℝ (p i-p j) (b i-b j))/‖p i-p j‖^3)+
        pairSecondVariation p b i j/2-(51/50)*‖b i-b j‖^3) ≤ coulombEnergy x := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j hj
    exact hpair i j (Finset.mem_Ioi.mp hj)
  have hlinear := stationary_linear_sphere_correction p x hp hx hstationary
  have hcube := displacement_pair_cubic_sum b hr hb
  have hexpand : pairSum (fun i j =>
      (‖p i-p j‖)⁻¹+(-(inner ℝ (p i-p j) (b i-b j))/‖p i-p j‖^3)+
        pairSecondVariation p b i j/2-(51/50)*‖b i-b j‖^3) =
      coulombEnergy p+pairSum (fun i j => -(inner ℝ (p i-p j) (b i-b j))/‖p i-p j‖^3)+
        pairSum (pairSecondVariation p b)/2-(51/50)*pairSum (fun i j => ‖b i-b j‖^3) := by
    simp only [pairSum, coulombEnergy, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_div, ← Finset.mul_sum]
  rw [hexpand] at hsum
  change pairSum (fun i j => -(inner ℝ (p i-p j) (b i-b j))/‖p i-p j‖^3) = _ at hlinear
  rw [hlinear] at hsum
  change (pairSum (pairSecondVariation p b)-(∑ i, radialCoefficient p i*‖b i‖^2))/2-
    (153/10)*rho^3 ≤ _
  nlinarith

theorem zero_penalty_energy_gap {rho gap : ℝ} (hr : 0 ≤ rho) (hr1 : rho ≤ 1/1000)
    (hgap : 1/40*rho^2-(153/10)*rho^3 ≤ gap) : rho^2/200 ≤ gap := by
  have hc : (1/200 : ℝ) ≤ 1/40-(153/10)*rho := by linarith
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg rho)
  nlinarith

end ThomsonN10.Local
