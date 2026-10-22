import EKG3.SieveWeightEnvelope
import EKG3.SieveWeightRounded

/-! Soundness of the finite supplement to the analytic lower bound.
All rounded weights are rounded down; the logarithm is bounded above by
its positive atanh series with an explicit geometric remainder. The kernel
checks themselves are in `SieveWeightFiniteChunk0` to `SieveWeightFiniteChunk17`. -/
namespace EKG3
open scoped BigOperators

lemma log_le_rationalLogUpper (n : ℕ) (hn : 1 ≤ n) :
    Real.log n ≤ (rationalLogUpper n : ℝ) := by
  let k := Nat.log 2 n
  let a := 2^k
  let t : ℝ := ((n : ℝ)-a)/((n : ℝ)+a)
  have ha : 0 < a := by dsimp [a]; positivity
  have han : a ≤ n := Nat.pow_log_le_self 2 (by omega)
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hanR : (a : ℝ) ≤ n := by exact_mod_cast han
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hq : (1+t)/(1-t) = (n : ℝ)/a := by
    dsimp [t]
    field_simp [haR.ne', ne_of_gt (add_pos hnR haR)]
    ring
  have h := Real.log_div_le_sum_range_add ht0 ht1 3
  rw [hq, Real.log_div hnR.ne' haR.ne'] at h
  have hloga : Real.log (a : ℝ) = (k : ℝ)*Real.log 2 := by
    simp [a, Nat.cast_pow, Real.log_pow]
  rw [hloga] at h
  norm_num [Finset.sum_range_succ] at h
  have h2 : (k : ℝ)*Real.log 2 ≤ (k : ℝ)*(693148/1000000) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    linarith [Real.log_two_lt_d9]
  change Real.log n ≤ _
  dsimp [rationalLogUpper]
  push_cast
  have hcast : (a : ℝ) = (2 : ℝ)^k := by simp [a]
  dsimp [t] at h
  rw [hcast] at h
  dsimp [k] at h h2
  linarith

lemma roundedSieveWeight_le (n : ℕ) :
    (roundedSieveWeight n : ℝ) ≤
      1000000 * (if Squarefree n then (n.totient : ℝ)⁻¹ else 0) := by
  by_cases hsq : Squarefree n
  · rw [roundedSieveWeight, ite_eq_left hsq, ite_eq_left hsq]
    have hn : 0 < n := Nat.pos_of_ne_zero hsq.ne_zero
    have hphi : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
    have hdiv := Nat.div_mul_le_self 1000000 n.totient
    have hdivR : ((1000000 / n.totient : ℕ) : ℝ) * n.totient ≤ 1000000 := by
      exact_mod_cast hdiv
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hphi).mpr hdivR
  · simp [roundedSieveWeight, hsq]

lemma roundedSieveSum_le (Q : ℕ) : (roundedSieveSum Q : ℝ) / 1000000 ≤ G Q := by
  have hsum (Q : ℕ) : (roundedSieveSum Q : ℝ) ≤ 1000000 * G Q := by
    induction Q with
    | zero => simp [roundedSieveSum, G]
    | succ Q ih =>
      have hG : G (Q+1) = G Q +
          (if Squarefree (Q+1) then ((Q+1).totient : ℝ)⁻¹ else 0) := by
        simp only [G, Finset.sum_filter]
        rw [Finset.sum_Icc_succ_top (by omega)]
      rw [roundedSieveSum, Nat.cast_add, hG, mul_add]
      exact add_le_add ih (roundedSieveWeight_le (Q+1))
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000)).mpr (by simpa [mul_comm] using hsum Q)

end EKG3
