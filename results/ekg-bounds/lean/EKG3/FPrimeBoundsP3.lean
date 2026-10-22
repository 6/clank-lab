import EKG3.P3TailNumerics
import EKG3.FNumericsP3

namespace EKG3.P3.FarTail
open EKG Real

theorem sqrt_prime_bound (hrs : TailPiBounds) {x : ℝ} (hx : 10^153 ≤ x) :
    realPrimeCount (sqrt x) ≤ (2*1.045/log x) * sqrt x := by
  obtain ⟨hl, hs, _⟩ := large_parameters hx
  have hthreshold : (10:ℝ)^76 ≤ sqrt x :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr ((by norm_num : ((10:ℝ)^76)^2 ≤ 10^153).trans hx)
  have h := hrs.2 (sqrt x) hthreshold
  rw [Real.log_sqrt (by linarith : 0 ≤ x)] at h
  convert h using 1; ring

noncomputable def primeCombination (n : ℕ) : ℝ :=
  Nat.primeCounting n - 2*(Nat.primeCounting (n/2) : ℝ) + Nat.primeCounting (n/3)

theorem real_count_div (n k : ℕ) :
    realPrimeCount ((n:ℝ)/(k:ℝ)) = Nat.primeCounting (n/k) := by
  simp [realPrimeCount, Nat.floor_div_eq_div]

theorem prime_combination_bounds (hrs : TailPiBounds) {n : ℕ}
    (hn : (10:ℝ)^153 ≤ n) :
    0 ≤ primeCombination n ∧ primeCombination n ≤ alpha n * n := by
  let x : ℝ := n
  obtain ⟨hl, hs, he⟩ := large_parameters hn
  have hx : 0 < x := by dsimp [x]; linarith
  have hL : 0 < log x := by dsimp [x]; linarith
  have h2 : 0 < log (x/2) := Real.log_pos (by dsimp [x]; linarith)
  have h3 : 0 < log (x/3) := Real.log_pos (by dsimp [x]; linarith)
  have hl2 : log (x/2) = log x - log 2 := Real.log_div hx.ne' (by norm_num)
  have hl3 : log (x/3) = log x - log 3 := Real.log_div hx.ne' (by norm_num)
  have h1lo := (hrs.1 x (by dsimp [x]; linarith))
  have h1hi := (hrs.2 x (by dsimp [x]; linarith))
  have h2lo := (hrs.1 (x/2) (by dsimp [x]; linarith))
  have h2hi := (hrs.2 (x/2) (by dsimp [x]; linarith))
  have h3lo := (hrs.1 (x/3) (by dsimp [x]; linarith))
  have h3hi := (hrs.2 (x/3) (by dsimp [x]; linarith))
  have hlog2 : 0 ≤ log 2 := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hlog3 : 0 ≤ log 3 := (Real.log_pos (by norm_num : (1:ℝ)<3)).le
  have hd2 : 0.921*x/(2*log x) ≤ realPrimeCount (x/2) := by
    have hd := div_le_div_of_nonneg_left (by linarith : 0 ≤ 0.921*(x/2)) h2
      (by rw [hl2]; linarith : log (x/2) ≤ log x)
    have hid : 0.921*x/(2*log x) = 0.921*(x/2)/log x := by ring
    rw [hid]; exact hd.trans h2lo
  have hd3 : 0.921*x/(3*log x) ≤ realPrimeCount (x/3) := by
    have hd := div_le_div_of_nonneg_left (by linarith : 0 ≤ 0.921*(x/3)) h3
      (by rw [hl3]; linarith : log (x/3) ≤ log x)
    have hid : 0.921*x/(3*log x) = 0.921*(x/3)/log x := by ring
    rw [hid]; exact hd.trans h3lo
  have hup2 : realPrimeCount (x/2) ≤ (2*0.921/3:ℝ)*(x/log x) := by
    apply h2hi.trans
    rw [hl2]
    apply (div_le_iff₀ (by linarith [h2] : 0 < log x-log 2)).mpr
    have hc : (1.045:ℝ)*log x ≤ (4*0.921/3:ℝ)*(log x-log 2) := by
      have hxL : (352.29551916:ℝ) < log x := hl
      linarith [Real.log_two_lt_d9]
    have hm := mul_le_mul_of_nonneg_left hc (div_nonneg hx.le hL.le)
    field_simp at hm ⊢
    nlinarith
  have eqn : primeCombination n =
      realPrimeCount x - 2*realPrimeCount (x/2) + realPrimeCount (x/3) := by
    change _ = realPrimeCount (n:ℝ) - 2*realPrimeCount ((n:ℝ)/(2:ℕ)) +
      realPrimeCount ((n:ℝ)/(3:ℕ))
    rw [real_count_div n 2, real_count_div n 3]
    simp [primeCombination, realPrimeCount]
  rw [eqn]
  constructor
  · have hid : 0.921*x/log x + 0.921*x/(3*log x) = 2*((2*0.921/3:ℝ)*(x/log x)) := by ring
    linarith
  · have hb : 1.045*x/log x - 2*(0.921*x/(2*log x)) +
        1.045*(x/3)/log (x/3) = alpha x * x := by
      rw [hl3]
      unfold alpha
      have h3' : log x - log 3 ≠ 0 := by rw [← hl3]; exact h3.ne'
      field_simp [hL.ne', h3']
    change _ ≤ alpha x * x
    linarith

end EKG3.P3.FarTail
