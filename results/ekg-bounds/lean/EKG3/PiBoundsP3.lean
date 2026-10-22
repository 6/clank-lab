import EKG3.P3Elementary
import EKG3.P3Integral
import IEANTN.RS12.Proof
import IEANTN.Chebyshev.Lower

namespace EKG3

open Real Chebyshev Set MeasureTheory intervalIntegral

theorem p3_psi_upper (x : ℝ) (hx : 0 < x) : psi x < p3C * x := by
  convert RS_prime.theorem_12 hx using 1
  norm_num [RS_prime.c₀, p3C]

theorem p3_psi_lower (x : ℝ) (hx : 30 ≤ x) :
    p3A * x - 5 * log x + 5 ≤ psi x := by
  have ha : p3A ≤ ChebyshevSol.a := by
    simpa only [p3A, show (0.92129 : ℝ) = 92129 / 100000 by norm_num] using
      ChebyshevSol.a_bound.1
  have h := mul_le_mul_of_nonneg_right ha (by linarith : 0 ≤ x)
  linarith [ChebyshevSol.psi_lower x hx]

theorem p3_theta_upper (x : ℝ) (hx : 0 < x) : theta x ≤ p3C * x :=
  (theta_le_psi x).trans (p3_psi_upper x hx).le

theorem p3_remainder (x : ℝ) (hx : 256 ≤ x) : psi x - theta x ≤ R3 x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ log x / log 2 :=
    div_nonneg (log_pos (by linarith)).le (log_pos (by norm_num)).le
  have hs := (p3_psi_upper (sqrt x) (sqrt_pos.mpr hx0)).le
  have hc := mul_le_mul_of_nonneg_left
    (p3_psi_upper (x ^ (1 / 3 : ℝ)) (rpow_pos_of_pos hx0 _)).le hlog
  have h := (p3_psi_sub_theta x hx).trans (add_le_add hs hc)
  convert h using 1
  unfold R3
  ring

theorem p3_pi_lower (x : ℝ) (hx : 256 ≤ x) : L3 x ≤ EKG.realPrimeCount x := by
  have hl : 0 < log x := log_pos (by linarith)
  have h := p3_psi_lower x (by linarith)
  have hr := p3_remainder x hx
  have ht := theta_le_pi_mul_log' x
  change theta x ≤ EKG.realPrimeCount x * log x at ht
  unfold L3
  apply max_le (by unfold EKG.realPrimeCount; positivity)
  apply (div_le_iff₀ hl).mpr
  linarith

theorem p3_pi_upper (x : ℝ) (hx : 256 ≤ x) : EKG.realPrimeCount x ≤ U3 x := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hc : 0 ≤ p3C := by norm_num [p3C]
  have hint : IntervalIntegrable
      (fun t : ℝ => theta t / (t * log t ^ 2)) volume 256 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      ((integrableOn_theta_div_id_mul_log_sq x).mono_set (by
        intro t ht; exact ⟨by linarith [ht.1], ht.2⟩))
  have hcont : ContinuousOn (fun t : ℝ => p3C * (1 / log t ^ 2)) (Icc 256 x) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have htlog : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  have hi2 : IntervalIntegrable (fun t : ℝ => p3C * (1 / log t ^ 2)) volume 256 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr hcont.integrableOn_Icc
  have hi := integral_mono_on hx hint hi2 (by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have htlog : 0 < log t := log_pos (by linarith [ht.1])
    calc
      theta t / (t * log t ^ 2) ≤ p3C * t / (t * log t ^ 2) :=
        div_le_div_of_nonneg_right (p3_theta_upper t ht0) (by positivity)
      _ = p3C * (1 / log t ^ 2) := by field_simp)
  rw [intervalIntegral.integral_const_mul] at hi
  have hm := mul_le_mul_of_nonneg_left (p3_integral_majorant x hx) hc
  have he := div_le_div_of_nonneg_right (p3_theta_upper x (by linarith))
    (log_pos (by linarith : 1 < x)).le
  rw [p3_partial_summation x hx]
  calc
    _ ≤ EKG.realPrimeCount 256 + p3C * x / log x - theta 256 / log 256 +
        p3C * (p3F x - x / log x - (p3F 256 - 256 / log 256)) := by linarith
    _ = U3 x := by unfold U3 p3J; ring

/-- Unconditional P3 bounds with the exact finite list at the join. -/
theorem piBoundsP3_holds : PiBoundsP3 :=
  ⟨primesBelow256_exact, p3_small_count,
    fun x hx => ⟨p3_remainder x hx, p3_pi_lower x hx, p3_pi_upper x hx⟩⟩

end EKG3
