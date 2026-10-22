import EKG3.SieveWeight
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace EKG3
open scoped BigOperators

lemma log_forty : Real.log 40 = 3 * Real.log 2 + Real.log 5 := by
  rw [show (40 : ℝ) = 2^3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num

lemma harmonic_forty_lower : (0.5645 : ℝ) < (harmonic 40 : ℝ) - Real.log 41 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 41/40)
  rw [Real.log_div (by norm_num) (by norm_num)] at h
  have h40 := log_forty
  have h2 := Real.log_two_lt_d9
  have h5 := Real.log_five_lt_d9
  norm_num [harmonic, Finset.sum_range_succ] at *
  linarith

lemma harmonic_forty_upper : (harmonic 40 : ℝ) - Real.log 40 < 0.59 := by
  have h40 := log_forty
  have h2 := Real.log_two_gt_d9
  have h5 := Real.log_five_gt_d9
  norm_num [harmonic, Finset.sum_range_succ] at *
  linarith

lemma harmonic_lower (n : ℕ) (hn : 40 ≤ n) :
    Real.log (n+1) + 0.5645 < (harmonic n : ℝ) := by
  have h := Real.strictMono_eulerMascheroniSeq.monotone hn
  dsimp [Real.eulerMascheroniSeq] at h
  have hc := harmonic_forty_lower
  norm_num at h hc
  linarith

lemma harmonic_upper (n : ℕ) (hn : 40 ≤ n) :
    (harmonic n : ℝ) < Real.log n + 0.59 := by
  have h := Real.strictAnti_eulerMascheroniSeq'.antitone hn
  have hn0 : n ≠ 0 := by omega
  simp only [Real.eulerMascheroniSeq', ite_eq_right hn0] at h
  have hc := harmonic_forty_upper
  norm_num at h hc
  linarith

lemma harmonic_div_lower (Q d : ℕ) (hd : 0 < d) (hQ : 40*d ≤ Q) :
    Real.log ((Q : ℝ)+1) - Real.log d + 0.5645 < (harmonic (Q/d) : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hk : 40 ≤ Q/d := (Nat.le_div_iff_mul_le hd).mpr hQ
  have hnat : Q+1 ≤ (Q/d+1)*d := by
    have hm := Nat.mod_lt Q hd
    have he := Nat.mod_add_div Q d
    nlinarith
  have hreal : (Q : ℝ)+1 ≤ (((Q/d : ℕ) : ℝ)+1)*(d : ℝ) := by exact_mod_cast hnat
  have hquot : ((Q : ℝ)+1)/(d : ℝ) ≤ ((Q/d : ℕ) : ℝ)+1 := (div_le_iff₀ hdR).mpr hreal
  have hlogs : Real.log ((Q : ℝ)+1) - Real.log d ≤ Real.log (((Q/d : ℕ) : ℝ)+1) := by
    rw [← Real.log_div (by positivity) hdR.ne']
    exact Real.log_le_log (by positivity) hquot
  linarith [harmonic_lower (Q/d) hk]

lemma harmonic_div_upper (Q d : ℕ) (hd : 0 < d) (hQ : 40*d ≤ Q) :
    (harmonic (Q/d) : ℝ) < Real.log ((Q : ℝ)+1) - Real.log d + 0.59 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hk : 40 ≤ Q/d := (Nat.le_div_iff_mul_le hd).mpr hQ
  have hkR : (0 : ℝ) < (Q/d : ℕ) := by exact_mod_cast (show 0 < Q/d by omega)
  have hnat := Nat.div_mul_le_self Q d
  have hreal : (((Q/d : ℕ) : ℝ))*(d : ℝ) ≤ Q := by exact_mod_cast hnat
  have hquot : ((Q/d : ℕ) : ℝ) ≤ ((Q : ℝ)+1)/(d : ℝ) :=
    (le_div_iff₀ hdR).mpr (by linarith)
  have hlogs : Real.log ((Q/d : ℕ) : ℝ) ≤ Real.log ((Q : ℝ)+1) - Real.log d := by
    rw [← Real.log_div (by positivity) hdR.ne']
    exact Real.log_le_log hkR hquot
  linarith [harmonic_upper (Q/d) hk]

end EKG3
