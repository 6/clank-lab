import EKG.VerifiedCounts
import EKG.Span
import EKG.Asymptotic
import EKG.Clock

namespace EKG

theorem even_not_tick {m : ℕ} (hm : 2 ∣ m) : ¬ spanTickValue m := by
  rintro ⟨p, hp, hp2, he⟩
  rw [he] at hm
  rcases Nat.prime_two.dvd_mul.mp hm with hthree | hpdiv
  · norm_num at hthree
  · exact hp2 ((hp.dvd_iff_eq (by decide : 2 ≠ 1)).mp hpdiv)

/-- The lower side of the maximum is also controlled: the even immediately
below the frontier has appeared and is not a tick. -/
theorem frontier_le_nonTickTop_add_two (s : GreedySeq) {t : ℕ} (ht : 1 ≤ t) :
    frontier s t ≤ nonTickTop s t + 2 := by
  have he := frontier_ge_four s ht
  have hpos : 0 < frontier s t-2 := by omega
  have heven : 2 ∣ frontier s t-2 := by
    obtain ⟨k, hk⟩ := (frontier_spec s t).2.1
    omega
  obtain ⟨i, hi, hv⟩ := smaller_even_used s (t := t) hpos heven (by omega)
  have hnt : ¬ spanTickValue (s.a i) := by rw [hv]; exact even_not_tick heven
  have hbound := nonTick_le_top s (by omega : i ≤ t) hnt
  omega

/-- Theorem 1(b) for the actual sequence, with the published structural input
now discharged by its Lean proof. -/
theorem nonTickTop_quadratic (s : GreedySeq) {t : ℕ} (ht : 8 ≤ t) :
    (nonTickTop s t : ℝ) - (frontier s t : ℝ) ≤
      2 * (earlyEvenCount s t + 1 : ℕ)^2 +
      2 * (earlyEvenCount s t + 1 : ℕ) *
        Real.sqrt ((earlyEvenCount s t + 1 : ℕ)^2 + (frontier s t : ℝ)) :=
  s.nonTickTop_quadratic_of_prime_pattern t
    (by have := frontier_ge_fourteen s ht; omega) (primeIntroductionPattern s)

/-- Uniform eventual count estimate in the frontier variable. -/
theorem eventually_early_count_bound (s : GreedySeq) :
    ∀ᶠ t : ℕ in Filter.atTop,
      ((earlyEvenCount s t+1 : ℕ) : ℝ) ≤ 793 * sqrtLogRate (frontier s t) := by
  have hf : Filter.Tendsto (fun t => (frontier s t : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop s)
  filter_upwards [hf.eventually eventually_bootstrap_count_bound] with t ht
  have hc := early_even_bound s t
  have hc' : ((earlyEvenCount s t+1 : ℕ) : ℝ) ≤
      12 * sqrtPrimeCount (frontier s t) + 721 := by
    have hn : ((earlyEvenCount s t+1 : ℕ) : ℝ) ≤
        12 * (Nat.primeCounting (Nat.sqrt (frontier s t)) : ℝ) + 721 := by
      exact_mod_cast (show earlyEvenCount s t+1 ≤
        12*Nat.primeCounting (Nat.sqrt (frontier s t))+721 by omega)
    simpa only [primeCounting_sqrt_nat_eq] using hn
  exact hc'.trans ht

theorem eventually_nonTickTop_log_span (s : GreedySeq) :
    ∀ᶠ t : ℕ in Filter.atTop,
      (nonTickTop s t : ℝ) - (frontier s t : ℝ) ≤
        (4 * 793^2 + 2 * 793 : ℝ) * logRate (frontier s t) := by
  have hf : Filter.Tendsto (fun t => (frontier s t : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop s)
  filter_upwards [eventually_early_count_bound s,
    Filter.eventually_ge_atTop (8 : ℕ),
    (Real.tendsto_log_atTop.comp hf).eventually
      (Filter.eventually_ge_atTop (1 : ℝ))] with t hc ht hl
  have hquad := nonTickTop_quadratic s ht
  exact hquad.trans (span_bound_of_count_bound (by positivity)
    (by positivity) (by norm_num) hl hc)

end EKG
