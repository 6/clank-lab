import Statement.LemmaF
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum

/-! Rational enclosures for the audited far-tail constants. All arithmetic
in this module is checked by the kernel; no external interval output is used. -/
namespace EKG3.FarTail
open Real EKG

noncomputable def kappa (x : ℝ) : ℝ := 24 * 1.25506 / log x + 721 / sqrt x
noncomputable def sigma (x : ℝ) : ℝ :=
  2 * kappa x ^ 2 + 2 * kappa x * sqrt (1 + kappa x ^ 2)
noncomputable def alpha (x : ℝ) : ℝ :=
  (1.25506 - 1) / log x + 1.25506 / (3 * (log x - log 3))
noncomputable def eta (x : ℝ) : ℝ :=
  (2 * 1.25506 / log x) * (26 * 1.25506 / log x + 725 / sqrt x)
noncomputable def gamma (x : ℝ) : ℝ := 52 * 1.25506 / log x + 1448 / sqrt x
noncomputable def upperClock (x : ℝ) : ℝ :=
  1 + kappa x / sqrt x + sigma x / 2 + 3 / x
noncomputable def lowerClock (x : ℝ) : ℝ := 1 - alpha x - eta x - 5 / x

theorem large_parameters {x : ℝ} (hx : 10^200 ≤ x) :
    (460.51701852 : ℝ) < log x ∧ (10^12 : ℝ) ≤ sqrt x ∧ (10^24 : ℝ) ≤ x := by
  have ht : (2.3025850926 : ℝ) < log 10 := by
    rw [Real.log_ten_eq]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hp : (0 : ℝ) < 10^200 := by positivity
  have hl := Real.strictMonoOn_log.monotoneOn hp (lt_of_lt_of_le hp hx) hx
  rw [Real.log_pow] at hl
  have hs : (10^12 : ℝ)^2 ≤ x := le_trans (by norm_num) hx
  exact ⟨by norm_num at hl; linarith,
    (Real.le_sqrt (by positivity) (by positivity)).mpr hs,
    le_trans (by norm_num) hx⟩

theorem numeric_bounds {x : ℝ} (hx : 10^200 ≤ x) :
    kappa x < 0.0654079 ∧ sigma x < 0.1396517 ∧
    alpha x < 0.0014645 ∧ eta x < 0.0003863 ∧ gamma x < 0.1417171 ∧
    upperClock x < 1.0698259 ∧ 0.9981493 < lowerClock x := by
  obtain ⟨hl, hs, he⟩ := large_parameters hx
  have hlp : 0 < log x := by linarith
  have hsp : 0 < sqrt x := by linarith
  have hep : 0 < x := by linarith
  have hb1 : (24 * 1.25506 / log x : ℝ) ≤ 24 * 1.25506 / 460.51701852 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl.le
  have hb2 : (721 / sqrt x : ℝ) ≤ 721 / 10^12 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have hk : kappa x < (0.065407877 : ℝ) := by
    dsimp [kappa]; norm_num at hb1 hb2 ⊢; linarith
  have hk0 : 0 ≤ kappa x := by unfold kappa; positivity
  have hksq : kappa x ^ 2 < (0.065407877 : ℝ)^2 := by nlinarith
  have hr : sqrt (1 + kappa x ^ 2) < (1.002136813 : ℝ) := by
    apply (Real.sqrt_lt' (by norm_num)).mpr
    nlinarith
  have hsig : sigma x < (0.1396517 : ℝ) := by
    have hm := mul_lt_mul hk hr.le
      (Real.sqrt_pos.2 (by positivity : 0 < 1 + kappa x ^ 2)) (by norm_num)
    dsimp [sigma]; nlinarith
  have ha1 : ((1.25506 - 1) / log x : ℝ) ≤ (1.25506 - 1) / 460.51701852 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl.le
  have ha2 : (1.25506 / (3*(log x - log 3)) : ℝ) ≤
      1.25506 / (3*(460.51701852 - 1.0986122888)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith [Real.log_three_lt_d9]
  have ha : alpha x < (0.001464471 : ℝ) := by
    dsimp [alpha]; norm_num at ha1 ha2 ⊢; linarith
  have het1 : (2 * 1.25506 / log x : ℝ) ≤ 2 * 1.25506 / 460.51701852 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl.le
  have het2 : (26 * 1.25506 / log x : ℝ) ≤ 26 * 1.25506 / 460.51701852 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl.le
  have het3 : (725 / sqrt x : ℝ) ≤ 725 / 10^12 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have het : eta x < (0.000386226 : ℝ) := by
    have hm := mul_le_mul het1 (add_le_add het2 het3)
      (by positivity : (0:ℝ) ≤ 26*1.25506/log x + 725/sqrt x) (by positivity)
    dsimp [eta]; norm_num at hm ⊢; linarith
  have hg1 : (52 * 1.25506 / log x : ℝ) ≤ 52 * 1.25506 / 460.51701852 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl.le
  have hg2 : (1448 / sqrt x : ℝ) ≤ 1448 / 10^12 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have hg : gamma x < (0.1417171 : ℝ) := by
    dsimp [gamma]; norm_num at hg1 hg2 ⊢; linarith
  have hu1 : kappa x / sqrt x ≤ 0.065407877 / 10^12 :=
    div_le_div₀ (by norm_num) hk.le (by norm_num) hs
  have hu2 : (3/x : ℝ) ≤ 3/10^24 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
  have hlo : (5/x : ℝ) ≤ 5/10^24 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
  refine ⟨lt_trans hk (by norm_num), hsig, lt_trans ha (by norm_num),
    lt_trans het (by norm_num), hg, ?_, ?_⟩
  · dsimp [upperClock]; norm_num at hu1 hu2 ⊢; linarith
  · dsimp [lowerClock]; norm_num at hlo ⊢; linarith

/-- Cross-multiplied endpoint checks, including the weakest (prime) lower
endpoint and the weakest (tick) upper endpoint. -/
theorem ratio_checks :
    (13:ℝ) * (2 * 1.0698259) < 28 ∧
    7 * (3/2:ℝ) < 12 * 0.9981493 ∧
    7 * (1+0.1396517:ℝ) < 12 * 0.9981493 ∧
    13 * ((1+0.1417171:ℝ)*1.0698259) < 28 ∧
    (10:ℝ)^200 * (1+0.1417171) < 9*10^202 ∧
    9*(10:ℝ)^202 < 13*((10:ℝ)^203-1)/14 := by norm_num

/-- The directed endpoint comparisons from the audited script, evaluated
at the rational enclosures above rather than floating-point values. -/
theorem endpoint_ratios :
    (13/28:ℝ) < 1/(2*1.0698259) ∧ 1/(2*0.9981493:ℝ) < 12/7 ∧
    (13/28:ℝ) < (3/2)/1.0698259 ∧ (3/2:ℝ)/0.9981493 < 12/7 ∧
    (13/28:ℝ) < 1/1.0698259 ∧
    (0.81870:ℝ) < 1/((1+0.1417171)*1.0698259) ∧
    (13/28:ℝ) < 1/((1+0.1417171)*1.0698259) ∧
    (1:ℝ)/0.9981493 < 12/7 ∧ (1+0.1396517:ℝ)/0.9981493 < 12/7 := by
  norm_num

end EKG3.FarTail
