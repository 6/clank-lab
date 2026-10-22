/- Adapted from proof/lean/ThomsonN9/LocalCoercivity.lean,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.BlockHessian
import ThomsonN10.Local.LocalStationarity
import ThomsonN10.Local.Certificates.DiagonalDominance

/-! Checked local energy conclusion, conditional on the explicit matrix certificate. -/

namespace ThomsonN10.Local

open Matrix

theorem flattenCoordinates_norm_sq (b : Configuration) :
    flattenCoordinates (fun i a => b i a) ⬝ᵥ flattenCoordinates (fun i a => b i a) =
      ∑ i, ‖b i‖^2 := by
  simp only [dotProduct, flattenCoordinates, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro a _
  rw [Real.norm_eq_abs, sq_abs, pow_two]

theorem secondVariation_lower_of_augmented_hessian (p b : Configuration)
    (hpositive : (constrainedHessian p+rotationColumns p*(rotationColumns p).transpose-
      (1/20 : ℝ) • (1 : Matrix (Fin 10 × Fin 3) (Fin 10 × Fin 3) ℝ)).PosSemidef)
    (hskew : ∀ a c : Fin 3, (∑ i, (b i a*p i c-b i c*p i a)) = 0) :
    (1/20 : ℝ)*(∑ i, ‖b i‖^2) ≤ constrainedSecondVariation p b := by
  have hR := rotationColumns_annihilate_skew p (fun i a => b i a) hskew
  have hkernel : (rotationColumns p*(rotationColumns p).transpose) *ᵥ
      flattenCoordinates (fun i a => b i a) = 0 := by
    simp only [← Matrix.mulVec_mulVec, hR, Matrix.mulVec_zero]
  have h := Certificates.quadratic_lower_on_augmentation_kernel
    (constrainedHessian p) (rotationColumns p*(rotationColumns p).transpose)
    (1/20) (flattenCoordinates (fun i a => b i a)) hpositive hkernel
  simpa only [flattenCoordinates_norm_sq, constrainedHessian_quadratic] using h

theorem candidate_local_energy_gap (r : CandidateParameter) (x : Configuration)
    (hx : ∀ i, ‖x i‖ = 1) {rho : ℝ} (hr : 0 ≤ rho) (hr1 : rho ≤ 1/1000)
    (hs : ∑ i, ‖x i-candidate r i‖^2 = rho^2)
    (hskew : ∀ a c : Fin 3,
      (∑ i, ((x i-candidate r i) a*candidate r i c-
        (x i-candidate r i) c*candidate r i a)) = 0)
    (hpositive : (constrainedHessian (candidate r)+
      rotationColumns (candidate r)*(rotationColumns (candidate r)).transpose-
      (1/20 : ℝ) • (1 : Matrix (Fin 10 × Fin 3) (Fin 10 × Fin 3) ℝ)).PosSemidef) :
    rho^2/200 ≤ coulombEnergy x-coulombEnergy (candidate r) := by
  have hsecond := secondVariation_lower_of_augmented_hessian
    (candidate r) (fun i => x i-candidate r i) hpositive hskew
  rw [hs] at hsecond
  have hgap := energy_gap_lower_algebraic (candidate r) x (candidate_unit r) hx
    (candidate_force_eq_radialCoefficient r)
    (fun _ _ hij => candidate_pair_distance_ge_one r hij.ne) hr (by linarith) hs
  apply zero_penalty_energy_gap hr hr1
  linarith

theorem candidate_local_equality (r : CandidateParameter) (x : Configuration)
    (hx : ∀ i, ‖x i‖ = 1) {rho : ℝ} (hr : 0 ≤ rho) (hr1 : rho ≤ 1/1000)
    (hs : ∑ i, ‖x i-candidate r i‖^2 = rho^2)
    (hskew : ∀ a c : Fin 3,
      (∑ i, ((x i-candidate r i) a*candidate r i c-
        (x i-candidate r i) c*candidate r i a)) = 0)
    (hpositive : (constrainedHessian (candidate r)+
      rotationColumns (candidate r)*(rotationColumns (candidate r)).transpose-
      (1/20 : ℝ) • (1 : Matrix (Fin 10 × Fin 3) (Fin 10 × Fin 3) ℝ)).PosSemidef)
    (he : coulombEnergy x ≤ coulombEnergy (candidate r)) : x = candidate r := by
  have hgap := candidate_local_energy_gap r x hx hr hr1 hs hskew hpositive
  have hrzero : rho = 0 := by nlinarith [sq_nonneg rho]
  have hsumzero : ∑ i, ‖x i-candidate r i‖^2 = 0 := by simpa [hrzero] using hs
  funext i
  have hi : ‖x i-candidate r i‖^2 ≤ ∑ j, ‖x j-candidate r j‖^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖x j-candidate r j‖) (Finset.mem_univ i)
  rw [hsumzero] at hi
  have hn : ‖x i-candidate r i‖ = 0 := by nlinarith [norm_nonneg (x i-candidate r i)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end ThomsonN10.Local
