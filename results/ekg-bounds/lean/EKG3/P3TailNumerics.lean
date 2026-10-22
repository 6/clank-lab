import EKG3.P3Elementary
import Mathlib.Analysis.Complex.ExponentialBounds

namespace EKG3.P3
open Real EKG

/-- Deliberately rounded coefficients, valid on the full real tail. -/
def TailPiBounds : Prop :=
  (∀ x : ℝ, 10^76 ≤ x → 0.921*x/log x ≤ realPrimeCount x) ∧
  (∀ x : ℝ, 10^76 ≤ x → realPrimeCount x ≤ 1.045*x/log x)

theorem tail_pi_parameters {x : ℝ} (hx : 10^76 ≤ x) :
    174 < log x ∧ 10^12 ≤ sqrt x ∧ 10^24 ≤ x := by
  have ht : (2.3025850926 : ℝ) < log 10 := by
    rw [Real.log_ten_eq]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hl := log_le_log (by positivity : (0 : ℝ) < 10^76) hx
  rw [Real.log_pow] at hl
  refine ⟨by norm_num at hl; linarith, ?_, le_trans (by norm_num) hx⟩
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr ((by norm_num : (10^12 : ℝ)^2 ≤ 10^76).trans hx)

theorem p3J_le : p3J ≤ 54 := by
  have hl : 0 < log (256 : ℝ) := log_pos (by norm_num)
  have hf : 256/log (256 : ℝ) ≤ p3F 256 := by
    unfold p3F
    have hbase : (0 : ℝ) ≤ 256/log 256 := by positivity
    have hfac : (1 : ℝ) ≤ 1+1/log 256+2/log 256^2+24/log 256^3 := by
      have : (0 : ℝ) ≤ 1/log 256+2/log 256^2+24/log 256^3 := by positivity
      linarith
    nlinarith
  have ht : 0 ≤ Chebyshev.theta (256 : ℝ) := Chebyshev.theta_nonneg _
  have hpi : realPrimeCount 256 = 54 := p3_pi256
  unfold p3J
  rw [hpi]
  have hn : 0 ≤ Chebyshev.theta (256 : ℝ)/log 256 := div_nonneg ht hl.le
  have hc : 0 ≤ p3C := by norm_num [p3C]
  nlinarith

theorem tailPiBounds_of_bounds (hp3 : PiBoundsP3) : TailPiBounds := by
  have log_sqrt (x : ℝ) (hx : 0 ≤ x) : log x ≤ 2*sqrt x := by
    have h := log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1/2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  constructor
  · intro x hx
    obtain ⟨hlog, hroot, hbig⟩ := tail_pi_parameters hx
    have hx0 : 0 < x := by linarith
    have hl0 : 0 < log x := by linarith
    have hs0 : 0 ≤ sqrt x := sqrt_nonneg _
    have hs2 : sqrt x ^ 2 = x := sq_sqrt hx0.le
    have hlog2 : (0.69 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
    have hlogroot := log_sqrt x hx0.le
    have hlog6 := log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1/6)
    have hrpow : x^(1/3 : ℝ)*x^(1/6 : ℝ) = sqrt x := by
      rw [← rpow_add hx0, show (1/3 : ℝ)+1/6=1/2 by norm_num, ← sqrt_eq_rpow]
    have hprod : x^(1/3 : ℝ)*log x ≤ 6*sqrt x := by
      have hm := mul_le_mul_of_nonneg_left hlog6 (rpow_nonneg hx0.le (1/3 : ℝ))
      norm_num only [div_eq_mul_inv, inv_div, inv_one, mul_one] at hm
      nlinarith [hrpow]
    have hc : (p3C/log 2 : ℝ) ≤ 1.51 := by
      apply (div_le_iff₀ (by linarith : 0 < log 2)).mpr
      norm_num [p3C]
      linarith
    have hR : R3 x ≤ 11*sqrt x := by
      have hm := mul_le_mul hc hprod
        (by positivity : (0 : ℝ) ≤ x^(1/3 : ℝ)*log x) (by norm_num : (0 : ℝ) ≤ 1.51)
      unfold R3
      norm_num [p3C] at *
      nlinarith
    have hlower := (hp3.2.2 x (by linarith)).2.1
    have hmax : (p3A*x-5*log x+5-R3 x)/log x ≤ L3 x := le_max_right _ _
    apply le_trans _ (hmax.trans hlower)
    apply (div_le_div_iff_of_pos_right hl0).mpr
    norm_num [p3A]
    nlinarith
  · intro x hx
    obtain ⟨hlog, hroot, hbig⟩ := tail_pi_parameters hx
    have hx0 : 0 < x := by linarith
    have hl0 : 0 < log x := by linarith
    have hlogroot := log_sqrt x hx0.le
    have hs2 : sqrt x ^ 2 = x := sq_sqrt hx0.le
    have h1 : (1/log x : ℝ) ≤ 1/174 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlog.le
    have h2 : (2/log x^2 : ℝ) ≤ 2/174^2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
    have h3 : (24/log x^3 : ℝ) ≤ 24/174^3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      exact pow_le_pow_left₀ (by norm_num) hlog.le 3
    have hcoef : p3C*(1+1/log x+2/log x^2+24/log x^3) ≤ 1.0449 := by
      norm_num [p3C] at *
      linarith
    have hmain : p3C*p3F x ≤ 1.0449*x/log x := by
      have hm := mul_le_mul_of_nonneg_right hcoef (div_nonneg hx0.le hl0.le)
      convert hm using 1 <;> (try unfold p3F) <;> ring
    have hoff : (54 : ℝ) ≤ 0.0001*x/log x := by
      apply (le_div_iff₀ hl0).mpr
      nlinarith
    have hu := (hp3.2.2 x (by linarith)).2.2
    unfold U3 at hu
    have hid : (1.0449 : ℝ)*x/log x+0.0001*x/log x=1.045*x/log x := by ring
    linarith only [hu, hmain, hoff, p3J_le, hid]

end EKG3.P3
