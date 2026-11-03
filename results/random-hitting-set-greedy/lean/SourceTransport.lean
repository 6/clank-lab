import SourceEndpoint
import LP

namespace ADG
open Finset Filter
open scoped Topology

 theorem sourceM_agrees (k : ℕ) : sourceM (k^10) = k := by
  unfold sourceM
  rw [Nat.cast_pow]
  have h := Real.pow_rpow_inv_natCast (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    (show (10 : ℕ) ≠ 0 by norm_num)
  norm_num at h
  rw [h]
  simp

 theorem sourceP_agrees (k : ℕ) : sourceP (k^10) = parameterP k := by
  unfold sourceP parameterP
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k)]
  norm_num [Real.rpow_neg (Nat.cast_nonneg k), Real.rpow_natCast]
  simp [inv_pow, div_eq_mul_inv, Nat.cast_pow]
  norm_cast

 theorem sourceM_nonneg (n : ℕ) : (0 : ℝ) ≤ sourceM n := Nat.cast_nonneg _

 theorem sourceM_le_rpow (n : ℕ) : (sourceM n : ℝ) ≤ (n : ℝ)^(1/10 : ℝ) :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

 theorem sourceP_nonneg (n : ℕ) : 0 ≤ sourceP n := by
  unfold sourceP
  positivity

 theorem sourceP_le_one_tenth {n : ℕ} (hn : 1 ≤ n) : sourceP n ≤ 1/10 := by
  unfold sourceP
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by norm_num)

 theorem sourceP_le_half {n : ℕ} (hn : 1 ≤ n) : sourceP n ≤ 1/2 := by
  linarith [sourceP_le_one_tenth hn]

 theorem sourceMP_le (n : ℕ) : (sourceM n : ℝ) * sourceP n ≤
    (n : ℝ)^(-(3/10 : ℝ)) / 10 := by
  by_cases hn : n = 0
  · subst n; norm_num [sourceM,sourceP]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  calc
    (sourceM n : ℝ) * sourceP n ≤ (n : ℝ)^(1/10 : ℝ) * sourceP n :=
      mul_le_mul_of_nonneg_right (sourceM_le_rpow n) (sourceP_nonneg n)
    _ = (n : ℝ)^(-(3/10 : ℝ)) / 10 := by
      unfold sourceP
      rw [← mul_div_assoc, ← Real.rpow_add hn']
      norm_num

 theorem sourceMP_tendsto_zero :
    Tendsto (fun n => (sourceM n : ℝ) * sourceP n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^(-(3/10 : ℝ)) / 10) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/10)).comp
      tendsto_natCast_atTop_atTop).div_const 10
  exact squeeze_zero (fun n => mul_nonneg (sourceM_nonneg n) (sourceP_nonneg n)) sourceMP_le ht

 theorem source_admissible : SourceAdmissible := by
  refine ⟨1/20, 1, 1/2, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have hg : ∀ᶠ n : ℕ in atTop, (10 : ℝ) ≤ (n : ℝ)^(1/10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/10)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 10
  filter_upwards [hg, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hone : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsmall : (n : ℝ)^(1/20 : ℝ) ≤ (n : ℝ)^(1/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
  have hfloor : (n : ℝ)^(1/10 : ℝ) / 2 < (sourceM n : ℝ) :=
    Nat.div_two_lt_floor (by linarith)
  have hupper : (sourceM n : ℝ) ≤ n := by
    apply le_trans (sourceM_le_rpow n)
    simpa using Real.rpow_le_rpow_of_exponent_le hone (by norm_num : (1/10 : ℝ) ≤ 1)
  have ha : 0 < (n : ℝ)^(2/5 : ℝ) := Real.rpow_pos_of_pos hnpos _
  have hexp : (n : ℝ)^(1/2 : ℝ) = (n : ℝ)^(2/5 : ℝ) * (n : ℝ)^(1/10 : ℝ) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have hden : (10 : ℝ) * (n : ℝ)^(2/5 : ℝ) ≤ (n : ℝ)^(1/2 : ℝ) := by
    rw [hexp]
    nlinarith
  have hlow : 1 / (n : ℝ)^(1/2 : ℝ) ≤ sourceP n := by
    unfold sourceP
    rw [Real.rpow_neg hnpos.le]
    calc
      _ ≤ 1 / (10 * (n : ℝ)^(2/5 : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) hden
      _ = ((n : ℝ)^(2/5 : ℝ))⁻¹ / 10 := by ring
  exact ⟨by nlinarith [Real.rpow_nonneg hnpos.le (1/10 : ℝ)], by simpa using hupper,
    hlow, sourceP_le_half hn1⟩

end ADG
