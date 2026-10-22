import Statement.PiBoundsP3

namespace EKG3

open Finset Real Chebyshev

theorem p3_pi256 : EKG.realPrimeCount 256 = 54 := by
  have h : Nat.primeCounting 256 = 54 := by decide +kernel
  norm_num [EKG.realPrimeCount, h]

theorem primesBelow256_exact (n : ℕ) :
    n ∈ primesBelow256 ↔ n.Prime ∧ n < 256 := by
  have h : primesBelow256.toFinset = (range 256).filter Nat.Prime := by
    decide +kernel
  rw [← List.mem_toFinset, h]
  simp only [mem_filter, mem_range]
  exact and_comm

theorem p3_small_count (x : ℝ) (hx : 0 ≤ x) (h256 : x < 256) :
    EKG.realPrimeCount x =
      ((primesBelow256.filter (fun p => p ≤ ⌊x⌋₊)).length : ℝ) := by
  have hn : ⌊x⌋₊ < 256 := (Nat.floor_lt hx).mpr (by exact_mod_cast h256)
  have hs : (range (⌊x⌋₊ + 1)).filter Nat.Prime =
      (primesBelow256.filter (fun p => p ≤ ⌊x⌋₊)).toFinset := by
    ext p
    simp only [mem_filter, mem_range, List.mem_toFinset, List.mem_filter,
      primesBelow256_exact, decide_eq_true_eq]
    constructor
    · rintro ⟨hp, hprime⟩
      exact ⟨⟨hprime, by omega⟩, by omega⟩
    · rintro ⟨⟨hprime, _⟩, hp⟩
      exact ⟨by omega, hprime⟩
  have hd : primesBelow256.Nodup := by decide +kernel
  simp only [EKG.realPrimeCount, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range, hs, List.toFinset_card_of_nodup (hd.filter _)]

/-- Isolate the square contribution and bound each higher power by the
cube-root contribution. This is the precise P3 psi-to-theta step. -/
theorem p3_psi_sub_theta (x : ℝ) (hx : 256 ≤ x) :
    psi x - theta x ≤
      psi (sqrt x) + (log x / log 2) * psi (x ^ (1 / 3 : ℝ)) := by
  let N : ℕ := ⌊log x / log 2⌋₊
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog : 0 ≤ log x / log 2 := div_nonneg (log_nonneg hx1) (log_pos (by norm_num)).le
  have hN : 2 ≤ N := by
    apply Nat.le_floor
    rw [le_div_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))]
    have h := log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ x)
    rw [show (4 : ℝ) = 2^2 by norm_num, log_pow] at h
    norm_num at h ⊢
    exact h
  have hexpand := psi_eq_theta_add_sum_theta (by linarith : 2 ≤ x)
  change psi x = theta x + ∑ n ∈ Icc 2 N, theta (x ^ ((1 : ℝ) / n)) at hexpand
  rw [hexpand, add_sub_cancel_left, ← add_sum_Ioc_eq_sum_Icc hN]
  simp only [Nat.cast_ofNat]
  have htwo : theta (x ^ (1 / 2 : ℝ)) ≤ psi (sqrt x) := by
    simpa only [sqrt_eq_rpow] using theta_le_psi (x ^ (1 / 2 : ℝ))
  have htail : (∑ n ∈ Ioc 2 N, theta (x ^ ((1 : ℝ) / n))) ≤
      (log x / log 2) * psi (x ^ (1 / 3 : ℝ)) := by
    calc
      _ ≤ ∑ _n ∈ Ioc 2 N, psi (x ^ (1 / 3 : ℝ)) := by
        apply sum_le_sum
        intro n hn
        have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1
        exact (theta_le_psi _).trans (psi_mono
          (rpow_le_rpow_of_exponent_le hx1 (by
            apply one_div_le_one_div_of_le (by norm_num) hn3)))
      _ = ((N - 2 : ℕ) : ℝ) * psi (x ^ (1 / 3 : ℝ)) := by
        simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul]
      _ ≤ (log x / log 2) * psi (x ^ (1 / 3 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (psi_nonneg _)
        have hsub : ((N - 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 2
        exact hsub.trans (Nat.floor_le hlog)
  exact add_le_add htwo htail

end EKG3
