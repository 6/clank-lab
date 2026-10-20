import EKG.VerifiedSpans

namespace EKG

theorem observed_tick_prime_lt_frontier (s : GreedySeq) {t p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hused : UsedBefore s.a (t+1) (3*p)) : p < frontier s t := by
  obtain ⟨i, hi, hv⟩ := hused
  obtain ⟨n, hn, hin, _⟩ := odd_prime_tick_unique s hp hp2 hv
  have hnidx := newPrime_index s hn hp2
  have hle : 2*p ≤ frontier s t := by
    rw [← firstMultiple_frontier s hn hp2]
    exact frontier_monotone s (by omega)
  have hp0 := hp.pos
  omega

theorem tickAbove_card_le_primeCounting (s : GreedySeq) (t : ℕ) :
    (Clock.tickAbove s t spanTickValue).card ≤ Nat.primeCounting (frontier s t) := by
  classical
  let R := (frontier s t+1).primesBelow
  have hcard : R.card = Nat.primeCounting (frontier s t) :=
    Nat.primesBelow_card_eq_primeCounting' _
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun m : ℕ => m/3)
  · intro m hm
    obtain ⟨hodd, p, hp, hp2, hv⟩ := Finset.mem_filter.mp hm
    have hvalues := (Finset.mem_filter.mp hodd).1
    have hused := (Clock.mem_usedValues s t m).mp hvalues
    have hsmall := observed_tick_prime_lt_frontier s hp hp2 (by rwa [hv] at hused)
    apply Nat.mem_primesBelow.mpr
    simpa only [hv, Nat.mul_div_right p (by decide : 0 < 3)] using
      (show p < frontier s t+1 ∧ p.Prime from
      ⟨by omega, hp⟩)
  · intro m hm n hn heq
    obtain ⟨_, p, _, _, hp⟩ := Finset.mem_filter.mp hm
    obtain ⟨_, q, _, _, hq⟩ := Finset.mem_filter.mp hn
    simp [hp, hq] at heq
    omega

/-- The manuscript clock error is reduced to proved prime, span, early-even
counts and the as-yet separately required missing-composite count. -/
theorem clock_abs_le_proved_counts (s : GreedySeq) (t : ℕ) :
    |(frontier s t : ℤ) - ((t+1 : ℕ) : ℤ)| ≤
      1 + 2 * (Nat.primeCounting (frontier s t) : ℤ) +
      ((Clock.holes s t).card : ℤ) + (earlyEvenCount s t : ℤ) +
      ((nonTickTop s t - frontier s t : ℕ) : ℤ) := by
  classical
  apply Clock.clock_abs_le_prime_and_span s t spanTickValue (nonTickTop s t)
    (tickAbove_card_le_primeCounting s t)
  intro m hm
  obtain ⟨hodd, hnt⟩ := Finset.mem_filter.mp hm
  have hvalues := (Finset.mem_filter.mp hodd).1
  obtain ⟨i, hi, hv⟩ := (Clock.mem_usedValues s t m).mp hvalues
  rw [← hv]
  exact nonTick_le_top s (by omega) (by rwa [hv])

end EKG
