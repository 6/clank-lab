import EKG.Asymptotic
import EKG.Clock
import EKG.Span
import EKG.VerifiedClock
import EKG.HoleCounting

/-! Assembly of the logarithmic frontier clock rate. The generic assembly
lemmas below expose all finite-count hypotheses; the final actual-sequence
theorems instantiate these with the verified combinatorial modules.
Time `t` always means a prefix containing exactly `t+1` terms. -/
namespace EKG

open Real Filter Asymptotics
open scoped Topology

theorem sqrtLogRate_le_logRate {x : ℝ} (hx : 1 < x) :
    sqrtLogRate x ≤ logRate x := by
  unfold sqrtLogRate logRate
  apply div_le_div_of_nonneg_right ?_ (Real.log_pos hx).le
  apply Real.sqrt_le_left (by linarith) |>.mpr
  nlinarith

theorem nat_sub_cast_le_of_difference_bound {a b : ℕ} {D : ℝ}
    (hD : 0 ≤ D) (h : (a : ℝ) - (b : ℝ) ≤ D) :
    ((a-b : ℕ) : ℝ) ≤ D := by
  by_cases hab : b ≤ a
  · rwa [Nat.cast_sub hab]
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero]
    exact hD

/-- All finite combinatorial inputs are explicit. In particular the hole
bound is a bound on the actual `Clock.holes` finset, not a rate oracle. -/
theorem frontier_error_isBigO_of_count_bounds (s : GreedySeq)
    (hClock : ∀ᶠ t : ℕ in atTop,
      |(frontier s t : ℝ) - ((t+1 : ℕ) : ℝ)| ≤
        1 + 2 * (Nat.primeCounting (frontier s t) : ℝ) +
        ((Clock.holes s t).card : ℝ) + (earlyEvenCount s t : ℝ) +
        ((nonTickTop s t-frontier s t : ℕ) : ℝ))
    (hHole : ∀ᶠ t : ℕ in atTop,
      (Clock.holes s t).card ≤ Nat.primeCounting (Nat.sqrt (frontier s t)) *
        (13 * Nat.primeCounting (Nat.sqrt (frontier s t)) + 725))
    (hEarly : ∀ᶠ t : ℕ in atTop,
      ((earlyEvenCount s t+1 : ℕ) : ℝ) ≤ 793 * sqrtLogRate (frontier s t))
    (hTop : ∀ᶠ t : ℕ in atTop,
      (nonTickTop s t : ℝ) - (frontier s t : ℝ) ≤
        (4 * 793^2 + 2 * 793 : ℝ) * logRate (frontier s t)) :
    (fun t : ℕ => (frontier s t : ℝ) - ((t+1 : ℕ) : ℝ)) =O[atTop]
      (fun t => logRate (frontier s t)) := by
  have hf : Tendsto (fun t => (frontier s t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop s)
  apply IsBigO.of_bound (2522600 : ℝ)
  filter_upwards [hClock, hHole, hEarly, hTop,
    hf.eventually eventually_realPrimeCount_le,
    hf.eventually eventually_holes_majorant_le,
    hf.eventually eventually_one_le_sqrtLogRate,
    hf.eventually (eventually_gt_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp hf).eventually (eventually_ge_atTop (1 : ℝ))]
    with t hclock hhole hearly htop hprime hholes hunit hx hlog
  change 1 ≤ Real.log (frontier s t : ℝ) at hlog
  have hr := logRate_nonneg hx
  have hs := sqrtLogRate_le_logRate hx
  have h1 : 1 ≤ logRate (frontier s t) := hunit.trans hs
  have hpi : (Nat.primeCounting (frontier s t) : ℝ) ≤
      3 * logRate (frontier s t) := by
    simpa only [realPrimeCount, Nat.floor_natCast] using hprime
  have hhole' : ((Clock.holes s t).card : ℝ) ≤
      4818 * logRate (frontier s t) := by
    have hc : ((Clock.holes s t).card : ℝ) ≤
        sqrtPrimeCount (frontier s t) * (13 * sqrtPrimeCount (frontier s t) + 725) := by
      have hcast := (Nat.cast_le (α := ℝ)).mpr hhole
      push_cast at hcast
      simpa only [primeCounting_sqrt_nat_eq] using hcast
    have hsmall := logSqRate_le_logRate (show 0 ≤ (frontier s t : ℝ) by positivity) hlog
    exact hc.trans (hholes.trans (mul_le_mul_of_nonneg_left hsmall (by norm_num)))
  have hearly' : (earlyEvenCount s t : ℝ) ≤ 793 * logRate (frontier s t) := by
    have hle : (earlyEvenCount s t : ℝ) ≤ ((earlyEvenCount s t+1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right (earlyEvenCount s t) 1)
    exact (hle.trans hearly).trans (mul_le_mul_of_nonneg_left hs (by norm_num))
  have hspan : ((nonTickTop s t-frontier s t : ℕ) : ℝ) ≤
      (4 * 793^2 + 2 * 793 : ℝ) * logRate (frontier s t) :=
    nat_sub_cast_le_of_difference_bound (mul_nonneg (by norm_num) hr) htop
  have hb : |(frontier s t : ℝ) - ((t+1 : ℕ) : ℝ)| ≤
      2522600 * logRate (frontier s t) := by
    calc
      _ ≤ _ := hclock
      _ ≤ _ := by nlinarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg hr] using hb

/-- Converts an established frontier-scale clock error into the requested
zero-based time-scale statement; frontier divergence is already proved. -/
theorem frontier_clock_rate_of_frontier_error (s : GreedySeq)
    (herr : (fun t : ℕ => (frontier s t : ℝ) - ((t+1 : ℕ) : ℝ)) =O[atTop]
      (fun t => logRate (frontier s t))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℕ in atTop,
      |(frontier s t : ℝ) - ((t+1 : ℕ) : ℝ)| ≤
        C * ((t+1 : ℕ) : ℝ) / Real.log ((t+1 : ℕ) : ℝ) := by
  have hf : Tendsto (fun t => (frontier s t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop s)
  have h := (logRate_error_transfer hf herr).2
  obtain ⟨C, hC, hb⟩ := h.exists_pos
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb.bound, eventually_ge_atTop (1 : ℕ)] with t ht ht1
  have htime : (1 : ℝ) < ((t+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < t+1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (logRate_nonneg htime)] at ht
  simpa only [logRate, mul_div_assoc] using ht

theorem frontier_clock_finite_bound_of_frontier_error (s : GreedySeq)
    (herr : (fun t : ℕ => (frontier s t : ℝ) - ((t+1 : ℕ) : ℝ)) =O[atTop]
      (fun t => logRate (frontier s t))) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      |(frontier s t : ℝ) - ((t+1 : ℕ) : ℝ)| ≤ C * logRate ((t+1 : ℕ) : ℝ) := by
  obtain ⟨C, hC, hb⟩ := frontier_clock_rate_of_frontier_error s herr
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  refine ⟨C, hC, N, fun t ht => ?_⟩
  simpa only [logRate, mul_div_assoc] using hN t ht

theorem eventually_frontier_comparable_of_frontier_error (s : GreedySeq)
    (herr : (fun t : ℕ => (frontier s t : ℝ) - ((t+1 : ℕ) : ℝ)) =O[atTop]
      (fun t => logRate (frontier s t))) :
    ∀ᶠ t : ℕ in atTop, ((t+1 : ℕ) : ℝ) / 2 ≤ (frontier s t : ℝ) ∧
      (frontier s t : ℝ) ≤ 2 * ((t+1 : ℕ) : ℝ) :=
  eventually_comparable_of_logRate_error
    (tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop s)) herr

/-- A useful intermediate interface with precisely the actual hole-count
obligation still visible. The remaining counts are verified theorems. -/
theorem frontier_error_isBigO_of_hole_bound (s : GreedySeq)
    (hHole : ∀ᶠ t : ℕ in atTop,
      (Clock.holes s t).card ≤ Nat.primeCounting (Nat.sqrt (frontier s t)) *
        (13 * Nat.primeCounting (Nat.sqrt (frontier s t)) + 725)) :
    (fun t : ℕ => (frontier s t : ℝ) - ((t+1 : ℕ) : ℝ)) =O[atTop]
      (fun t => logRate (frontier s t)) := by
  apply frontier_error_isBigO_of_count_bounds s ?_ hHole
    (eventually_early_count_bound s) (eventually_nonTickTop_log_span s)
  exact Filter.Eventually.of_forall (fun t => by
    exact_mod_cast clock_abs_le_proved_counts s t)

/-- The frontier-scale clock error for every actual greedy EKG sequence.
The missing-composite count is discharged by its finite grouping proof. -/
theorem frontier_error_isBigO (s : GreedySeq) :
    (fun t : ℕ => (frontier s t : ℝ) - ((t+1 : ℕ) : ℝ)) =O[atTop]
      (fun t => logRate (frontier s t)) := by
  apply frontier_error_isBigO_of_hole_bound s
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with t ht
  exact Clock.holes_card_bound s ht

/-- The manuscript frontier clock rate, unconditionally and with the
zero-based prefix length `t+1` kept explicit. -/
theorem frontier_clock_rate (s : GreedySeq) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      |(frontier s t : ℝ) - ((t+1 : ℕ) : ℝ)| ≤ C * logRate ((t+1 : ℕ) : ℝ) :=
  frontier_clock_finite_bound_of_frontier_error s (frontier_error_isBigO s)

theorem eventually_frontier_clock_rate (s : GreedySeq) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℕ in atTop,
      |(frontier s t : ℝ) - ((t+1 : ℕ) : ℝ)| ≤
        C * ((t+1 : ℕ) : ℝ) / Real.log ((t+1 : ℕ) : ℝ) :=
  frontier_clock_rate_of_frontier_error s (frontier_error_isBigO s)

theorem eventually_frontier_comparable (s : GreedySeq) :
    ∀ᶠ t : ℕ in atTop, ((t+1 : ℕ) : ℝ) / 2 ≤ (frontier s t : ℝ) ∧
      (frontier s t : ℝ) ≤ 2 * ((t+1 : ℕ) : ℝ) :=
  eventually_frontier_comparable_of_frontier_error s (frontier_error_isBigO s)

theorem actual_frontier_clock_rate :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      |(frontier canonical t : ℝ) - ((t+1 : ℕ) : ℝ)| ≤
        C * logRate ((t+1 : ℕ) : ℝ) := frontier_clock_rate canonical

end EKG
