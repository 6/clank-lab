/- Adapted from proof/lean/ThomsonN9/LocalStationarity.lean,
 aravindkarthigeyan/thomson-n9-lean @
 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.CandidateGeometry
import ThomsonN10.Local.LocalEnergy
namespace ThomsonN10.Local

noncomputable def orbitWeight (a b c d e f g : ℝ) : Fin 10 → Fin 10 → ℝ :=
  fun i j => (![0,a,b,c,d,e,f,g] : Fin 8 → ℝ) (pairClass i j)

set_option maxHeartbeats 2000000 in
theorem orbit_force_balance (h a b c d e f g : ℝ)
    (hrel : b-c+2*h*(d+e)-h*(Real.sqrt 2+2)*f+h*(Real.sqrt 2-2)*g = 0)
    (i : Fin 10) :
    (∑ j, orbitWeight a b c d e f g i j • (candidateAt h j-candidateAt h i)) =
      (if i.val < 2 then -2*a+4*(h-1)*b+4*(-h-1)*c
       else -b-c-2*d-2*e+(Real.sqrt 2-2)*f-(Real.sqrt 2+2)*g) • candidateAt h i := by
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsf : rho h*f*((Real.sqrt 2)^2-2) = 0 := by rw [hs]; ring
  have hsg : rho h*g*((Real.sqrt 2)^2-2) = 0 := by rw [hs]; ring
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [orbitWeight, pairClass, candidateAt, vec, q, Fin.sum_univ_succ] <;>
    nlinarith

noncomputable def classWeight (h : ℝ) (k : Fin 8) : ℝ :=
  (Real.sqrt (pairSq h k))⁻¹^3

theorem candidate_force_relation (h : CandidateParameter) :
    classWeight h 2-classWeight h 3+
      2*(h : ℝ)*(classWeight h 4+classWeight h 5)-
      (h : ℝ)*(Real.sqrt 2+2)*classWeight h 6+
      (h : ℝ)*(Real.sqrt 2-2)*classWeight h 7 = 0 := by
  obtain ⟨hl,hu⟩ := height_bounds h
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsp : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hr : 0 < rho h := Real.sqrt_pos.mpr (by nlinarith)
  have hr2 : (rho h)^2 = 1-(h : ℝ)^2 := Real.sq_sqrt (by nlinarith)
  have hd4 : Real.sqrt (2*(1-(h : ℝ)^2)) = Real.sqrt 2*rho h := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rfl
  have hd5 : Real.sqrt (4*(1-(h : ℝ)^2)) = 2*rho h := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num [rho]
  have hfirst : 2*(h : ℝ)*(classWeight h 4+classWeight h 5) =
      (4*Real.sqrt 2+2)*(h : ℝ)/(8*((1-(h : ℝ)^2)*rho h)) := by
    change 2*(h : ℝ)*((Real.sqrt (2*(1-(h : ℝ)^2)))⁻¹^3+
      (Real.sqrt (4*(1-(h : ℝ)^2)))⁻¹^3) = _
    rw [hd4,hd5,← hr2]
    field_simp [hr.ne', hsp.ne']
    ring_nf
    have hs4 : (Real.sqrt 2)^4 = (4 : ℝ) := by
      calc
        _ = ((Real.sqrt 2)^2)^2 := by ring
        _ = 4 := by rw [hs]; norm_num
    rw [hs4]
    ring
  rw [hfirst]
  have hstat := h.property.2.2
  unfold stationarity at hstat
  have hnear : 0 < 2-Real.sqrt 2+(2+Real.sqrt 2)*(h : ℝ)^2 := by
    have hb : Real.sqrt 2 < (3/2 : ℝ) := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
    have hc : 0 ≤ (2+Real.sqrt 2)*(h : ℝ)^2 := by positivity
    nlinarith
  have hfar : 0 < 2+Real.sqrt 2+(2-Real.sqrt 2)*(h : ℝ)^2 := by
    have hb : Real.sqrt 2 < (3/2 : ℝ) := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
    have hc : 0 ≤ (2-Real.sqrt 2)*(h : ℝ)^2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have h2p : 0 < 2-2*(h : ℝ) := by linarith
  have h3p : 0 < 2+2*(h : ℝ) := by linarith
  have hroot (t : ℝ) (ht : 0 < t) : (Real.sqrt t)⁻¹^3 = 1/(t*Real.sqrt t) := by
    have hs := Real.sq_sqrt ht.le
    have hp := Real.sqrt_pos.mpr ht
    field_simp
    nlinarith
  change (Real.sqrt (2-2*(h : ℝ)))⁻¹^3-(Real.sqrt (2+2*(h : ℝ)))⁻¹^3+
    (4*Real.sqrt 2+2)*(h : ℝ)/(8*((1-(h : ℝ)^2)*rho h))-
    (h : ℝ)*(Real.sqrt 2+2)*(Real.sqrt (2-Real.sqrt 2+(2+Real.sqrt 2)*(h : ℝ)^2))⁻¹^3+
    (h : ℝ)*(Real.sqrt 2-2)*(Real.sqrt (2+Real.sqrt 2+(2-Real.sqrt 2)*(h : ℝ)^2))⁻¹^3 = 0
  rw [hroot _ h2p,hroot _ h3p,hroot _ hnear,hroot _ hfar]
  convert congrArg (fun x : ℝ => x/8) hstat using 1 <;>
    simp only [rho, div_eq_mul_inv, mul_inv_rev, inv_div, inv_mul_cancel₀] <;> ring


theorem candidate_force_radial (h : CandidateParameter) (i : Fin 10) :
    ∃ lambda : ℝ, coulombForce (candidate h) i = lambda • candidate h i := by
  let w := classWeight h
  have hweight (i j : Fin 10) : (‖candidate h i-candidate h j‖)⁻¹^3 =
      orbitWeight (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) i j := by
    rw [candidate_distance]
    change w (pairClass i j) = _
    unfold orbitWeight
    generalize pairClass i j = k
    fin_cases k <;> simp [w,classWeight,pairSq]
  refine ⟨if i.val < 2 then -2*w 1+4*((h : ℝ)-1)*w 2+4*(-(h : ℝ)-1)*w 3
    else -w 2-w 3-2*w 4-2*w 5+(Real.sqrt 2-2)*w 6-(Real.sqrt 2+2)*w 7, ?_⟩
  unfold coulombForce
  simp_rw [hweight]
  exact orbit_force_balance h (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7)
    (candidate_force_relation h) i

theorem candidate_force_eq_radialCoefficient (h : CandidateParameter) (i : Fin 10) :
    coulombForce (candidate h) i = radialCoefficient (candidate h) i • candidate h i := by
  obtain ⟨lambda,hlambda⟩ := candidate_force_radial h i
  have hi := coulombForce_inner_self (candidate h) (candidate_unit h) i
  rw [hlambda,real_inner_smul_right,real_inner_self_eq_norm_sq,candidate_unit h i] at hi
  have heq : lambda = radialCoefficient (candidate h) i := by simpa using hi
  simpa only [heq] using hlambda

end ThomsonN10.Local
