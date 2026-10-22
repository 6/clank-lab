/- Adapted from targets/thomson-10/lp-formal/n10/Thomson10/Scalar.lean (supplied accepted N10 LP proof). N9 design: aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, proof/lean/ThomsonN9/LP/Concrete.lean. -/
import ThomsonN10.Cert.LP.Data

open scoped BigOperators
noncomputable section
namespace ThomsonN10.Cert.LP

 theorem q_nonneg (t : ℝ) (ht : -1 ≤ t ∧ t ≤ 1) : 0 ≤ q t := by
  unfold q
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (qCoeff_nonneg j)
  apply bern_nonneg <;> linarith [ht.1, ht.2]

 theorem minorant (t d : ℝ) (ht : -1 ≤ t ∧ t ≤ 1) (hd : 0 < d)
    (hsq : d^2 = 2-2*t) : h t ≤ d⁻¹ := by
  have hp : 0 ≤ (t+1)*(t+17/32)^2*(t-23/72)^2*q t := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith [ht.1]) (sq_nonneg _))
      (sq_nonneg _)) (q_nonneg t ht)
  have hh : (d*h t)^2 ≤ 1 := by
    rw [mul_pow, hsq]
    linarith [minorant_identity t]
  have hh' : d*h t ≤ 1 := by nlinarith [sq_nonneg (d*h t-1)]
  rw [inv_eq_one_div, le_div_iff₀ hd]
  nlinarith

 theorem residual_positive (t : ℝ) (ht : 13/20 ≤ t ∧ t ≤ 1) :
    0 < 1-(2-2*t)*(h t+51/1000)^2 := by
  rw [residual_identity]
  have hs : 0 ≤ ∑ j : Fin 10, (rCoeff j-rCoeff 0)*bern 9 ((20*t-13)/7) j := by
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (rCoeff_shift_nonneg j)
    apply bern_nonneg <;> linarith [ht.1, ht.2]
  have hc : 0 < rCoeff 0 := by norm_num [rCoeff]
  linarith

 theorem residual_bonus (t d : ℝ) (ht : 13/20 ≤ t ∧ t ≤ 1) (hd : 0 < d)
    (hsq : d^2 = 2-2*t) : 51/1000 < d⁻¹-h t := by
  have hh : (d*(h t+51/1000))^2 < 1 := by
    rw [mul_pow, hsq]
    linarith [residual_positive t ht]
  have hh' : d*(h t+51/1000) < 1 := by
    nlinarith [sq_nonneg (d*(h t+51/1000)-1)]
  have hh'' : h t+51/1000 < d⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hd]
    nlinarith
  linarith

end ThomsonN10.Cert.LP
