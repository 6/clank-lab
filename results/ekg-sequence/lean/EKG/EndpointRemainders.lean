import EKG.ClockRates
import EKG.CountingExact
import EKG.PartA

/-! The actual finite counting remainders at the canonical frontier.
The hole and early-even estimates are the proved Haver foundation bounds;
the odd non-tick count uses the completed canonical Part A theorem. -/
namespace EKG.CanonicalEndpoint

open Filter Asymptotics
open EKG.CanonicalCounting

private theorem canonical_frontier_real_tendsto :
    Tendsto (fun t : ℕ => (frontier canonical t : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop canonical)

theorem canonical_H_littleO :
    (fun t : ℕ => (H t : ℝ)) =o[atTop]
      (fun t => logRate (frontier canonical t : ℝ)) := by
  have hbound : (fun t : ℕ => (H t : ℝ)) =O[atTop]
      (fun t => sqrtPrimeCount (frontier canonical t : ℝ) *
        (13 * sqrtPrimeCount (frontier canonical t : ℝ) + 725)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (8 : ℕ)] with t ht
    have hc := (Nat.cast_le (α := ℝ)).mpr (Clock.holes_card_bound canonical ht)
    push_cast at hc
    have hc' : (H t : ℝ) ≤ sqrtPrimeCount (frontier canonical t : ℝ) *
        (13 * sqrtPrimeCount (frontier canonical t : ℝ) + 725) := by
      simpa only [H, primeCounting_sqrt_nat_eq] using hc
    have hnonneg : 0 ≤ sqrtPrimeCount (frontier canonical t : ℝ) *
        (13 * sqrtPrimeCount (frontier canonical t : ℝ) + 725) := by
      unfold sqrtPrimeCount realPrimeCount
      positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (H t : ℝ) by positivity),
      abs_of_nonneg hnonneg, one_mul] using hc'
  exact hbound.trans_isLittleO
    (holes_majorant_isLittleO_logRate.comp_tendsto canonical_frontier_real_tendsto)

theorem canonical_K_littleO :
    (fun t : ℕ => (K t : ℝ)) =o[atTop]
      (fun t => logRate (frontier canonical t : ℝ)) := by
  have hbound : (fun t : ℕ => (K t : ℝ)) =O[atTop]
      (fun t => sqrtLogRate (frontier canonical t : ℝ)) := by
    apply IsBigO.of_bound 793
    filter_upwards [eventually_early_count_bound canonical,
      canonical_frontier_real_tendsto.eventually (eventually_gt_atTop (1 : ℝ))]
      with t ht he
    have hle : (K t : ℝ) ≤ ((earlyEvenCount canonical t + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show earlyEvenCount canonical t ≤ earlyEvenCount canonical t + 1
        from Nat.le_add_right _ _)
    have hc := hle.trans ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (K t : ℝ) by positivity),
      abs_of_nonneg (sqrtLogRate_nonneg he)] using hc
  exact hbound.trans_isLittleO
    (sqrtLogRate_isLittleO_logRate.comp_tendsto canonical_frontier_real_tendsto)

/-- This cardinal bound uses every observed non-tick odd value and introduces
no sparsity assumption: injectivity bounds it by the full integer span. -/
theorem canonical_O_le_upper_excursion (t : ℕ) :
    (O t : ℝ) ≤
      max ((nonTickTop canonical t : ℝ) - (frontier canonical t : ℝ)) 0 := by
  classical
  have hcard : O t ≤ nonTickTop canonical t - frontier canonical t := by
    apply Clock.nonTickOddAbove_card_le_span canonical t spanTickValue
      (nonTickTop canonical t)
    intro m hm
    obtain ⟨hodd, hnot⟩ := Finset.mem_filter.mp hm
    have hused := (Finset.mem_filter.mp hodd).1
    obtain ⟨i, hi, hv⟩ := (Clock.mem_usedValues canonical t m).mp hused
    have hnt : ¬ spanTickValue (canonical.a i) := by rwa [hv]
    have htop := nonTick_le_top canonical (by omega : i ≤ t) hnt
    rwa [hv] at htop
  have hcast := (Nat.cast_le (α := ℝ)).mpr hcard
  exact hcast.trans (nat_sub_cast_le_of_difference_bound
    (le_max_right _ _) (le_max_left _ _))

theorem canonical_O_littleO :
    (fun t : ℕ => (O t : ℝ)) =o[atTop]
      (fun t => logRate (frontier canonical t : ℝ)) := by
  apply IsLittleO.of_bound
  intro δ hδ
  obtain ⟨u0, hu0⟩ := PartA.canonical_upper_excursion δ hδ
  filter_upwards [eventually_ge_atTop u0,
    canonical_frontier_real_tendsto.eventually (eventually_gt_atTop (1 : ℝ))]
    with t ht he
  have hc : (O t : ℝ) ≤ δ * logRate (frontier canonical t : ℝ) := by
    apply (canonical_O_le_upper_excursion t).trans
    simpa only [logRate, mul_div_assoc] using hu0 t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (O t : ℝ) by positivity),
    abs_of_nonneg (logRate_nonneg he)] using hc

theorem canonical_correction_littleO :
    (fun t : ℕ => (correction t : ℝ)) =o[atTop]
      (fun t => logRate (frontier canonical t : ℝ)) := by
  have hbound : (fun t : ℕ => (correction t : ℝ)) =O[atTop]
      (fun t => sqrtLogRate (frontier canonical t : ℝ)) := by
    apply IsBigO.of_bound 5
    filter_upwards [eventually_ge_atTop (8 : ℕ),
      canonical_frontier_real_tendsto.eventually eventually_one_le_sqrtLogRate]
      with t ht hr
    have hc : (correction t : ℝ) ≤ 5 := by
      exact_mod_cast (correction_bounds t ht).2
    have hc' : (correction t : ℝ) ≤ 5 * sqrtLogRate (frontier canonical t : ℝ) := by
      linarith
    have hnonneg : 0 ≤ sqrtLogRate (frontier canonical t : ℝ) := by linarith
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (correction t : ℝ) by positivity),
      abs_of_nonneg hnonneg] using hc'
  exact hbound.trans_isLittleO
    (sqrtLogRate_isLittleO_logRate.comp_tendsto canonical_frontier_real_tendsto)

theorem canonical_counting_remainder_littleO :
    (fun t : ℕ => (H t : ℝ) - (K t : ℝ) - (O t : ℝ) + (correction t : ℝ))
      =o[atTop] (fun t => logRate (frontier canonical t : ℝ)) :=
  ((canonical_H_littleO.sub canonical_K_littleO).sub canonical_O_littleO).add
    canonical_correction_littleO

end EKG.CanonicalEndpoint
