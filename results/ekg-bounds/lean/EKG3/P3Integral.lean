import Statement.PiBoundsP3
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.ExponentialBounds

namespace EKG3

open Real Set MeasureTheory intervalIntegral

private noncomputable def G (x : ℝ) : ℝ :=
  x / log x ^ 2 + 2 * (x / log x ^ 3) + 24 * (x / log x ^ 4)

private theorem G_eq (x : ℝ) (h : log x ≠ 0) :
    G x = p3F x - x / log x := by
  unfold G p3F
  field_simp
  ring

private theorem G_deriv {x : ℝ} (hx : 256 ≤ x) :
    HasDerivAt G (1 / log x ^ 2 + 18 / log x ^ 4 - 96 / log x ^ 5) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl : log x ≠ 0 := ne_of_gt (log_pos (by linarith))
  have hd (n : ℕ) :=
    (hasDerivAt_id x).div ((hasDerivAt_log hx0).pow n) (pow_ne_zero n hl)
  convert ((hd 2).add ((hd 3).const_mul 2)).add ((hd 4).const_mul 24) using 1
  · rfl
  · simp only [Pi.pow_apply, id_eq]
    field_simp
    ring

private theorem log_lower {x : ℝ} (hx : 256 ≤ x) : (16 / 3 : ℝ) ≤ log x := by
  have h := log_le_log (by norm_num : (0 : ℝ) < 256) hx
  rw [show (256 : ℝ) = 2 ^ 8 by norm_num, log_pow] at h
  norm_num at h
  linarith [Real.log_two_gt_d9]

/-- The explicit antiderivative majorant used in P3's upper bound. -/
theorem p3_integral_majorant (x : ℝ) (hx : 256 ≤ x) :
    (∫ t in (256 : ℝ)..x, 1 / log t ^ 2) ≤
      p3F x - x / log x - (p3F 256 - 256 / log 256) := by
  have hcont : ContinuousOn G (Icc 256 x) := by
    intro t ht
    exact (G_deriv ht.1).continuousAt.continuousWithinAt
  have hint : IntegrableOn (fun t : ℝ => 1 / log t ^ 2) (Icc 256 x) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have htlog : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  have h := integral_le_sub_of_hasDeriv_right_of_le hx hcont
    (fun t ht => (G_deriv ht.1.le).hasDerivWithinAt) hint (by
      intro t ht
      have hl : 0 < log t := log_pos (by linarith [ht.1])
      have hl16 := log_lower ht.1.le
      have heq : 18 / log t ^ 4 - 96 / log t ^ 5 =
          (18 * log t - 96) / log t ^ 5 := by field_simp
      have hp : 0 ≤ (18 * log t - 96) / log t ^ 5 :=
        div_nonneg (by linarith) (le_of_lt (pow_pos hl _))
      linarith [heq])
  rw [G_eq x (ne_of_gt (log_pos (by linarith))),
    G_eq 256 (ne_of_gt (log_pos (by norm_num)))] at h
  exact h

/-- Abel summation at the exact joining point a = 256. -/
theorem p3_partial_summation (x : ℝ) (hx : 256 ≤ x) :
    EKG.realPrimeCount x = EKG.realPrimeCount 256 +
      Chebyshev.theta x / log x - Chebyshev.theta 256 / log 256 +
        ∫ t in (256 : ℝ)..x, Chebyshev.theta t / (t * log t ^ 2) := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hi := Chebyshev.integrableOn_theta_div_id_mul_log_sq x
  have hix : IntervalIntegrable
      (fun t : ℝ => Chebyshev.theta t / (t * log t ^ 2)) volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx2).mpr hi
  have hi256 : IntervalIntegrable
      (fun t : ℝ => Chebyshev.theta t / (t * log t ^ 2)) volume 2 256 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq 256)
  have hix256 := hix.symm.trans hi256
  have hs := integral_add_adjacent_intervals hi256 hix256.symm
  have h1 := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2
  have h0 := Chebyshev.primeCounting_eq_theta_div_log_add_integral
    (by norm_num : (2 : ℝ) ≤ 256)
  change EKG.realPrimeCount x = _ at h1
  change EKG.realPrimeCount 256 = _ at h0
  linarith

end EKG3
