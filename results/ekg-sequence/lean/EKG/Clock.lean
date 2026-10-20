import EKG.Frontier
import EKG.PrimeStructurePermutation
import Mathlib.Order.Filter.AtTopBot.Basic

/-! The unconditional finite clock identity, with zero-based time: the prefix
at time `t` has exactly `t+1` terms. Prime-interval and tick-pattern counts are
separate explicit inputs to the final transfer theorem. -/
namespace EKG

/-- All positive integers in a fixed finite interval have appeared by a
common finite time. This uses the proved permutation theorem. -/
theorem finite_positive_interval_eventually_used (s : GreedySeq) (B : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ m, 0 < m → m ≤ B → UsedBefore s.a (t+1) m := by
  classical
  let hit := fun j : ℕ => Nat.find (every_positive_occurs s (Nat.succ_pos j))
  let T := (Finset.range B).sup hit
  refine ⟨T, ?_⟩
  intro t ht m hm hB
  have hindex : m-1 ∈ Finset.range B := Finset.mem_range.mpr (by omega)
  have hbound : hit (m-1) ≤ T := Finset.le_sup hindex
  have hval : s.a (hit (m-1)) = m := by
    have h := Nat.find_spec (every_positive_occurs s (Nat.succ_pos (m-1)))
    have he : m-1+1 = m := by omega
    simpa only [hit, Nat.succ_eq_add_one, he] using h
  exact ⟨hit (m-1), by omega, hval⟩

theorem frontier_eventually_gt (s : GreedySeq) (B : ℕ) :
    ∃ T, ∀ t, T ≤ t → B < frontier s t := by
  obtain ⟨T, hT⟩ := finite_positive_interval_eventually_used s B
  refine ⟨T, ?_⟩
  intro t ht
  by_contra h
  have hp := frontier_spec s t
  exact hp.2.2 (hT t ht _ hp.1 (by omega))

theorem frontier_unbounded (s : GreedySeq) (B : ℕ) :
    ∃ t, B < frontier s t := by
  obtain ⟨T, hT⟩ := frontier_eventually_gt s B
  exact ⟨T, hT T le_rfl⟩

theorem frontier_tendsto_atTop (s : GreedySeq) :
    Filter.Tendsto (frontier s) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro B
  obtain ⟨T, hT⟩ := frontier_eventually_gt s B
  exact ⟨T, fun t ht => (hT t ht).le⟩

theorem actual_frontier_tendsto_atTop :
    Filter.Tendsto (frontier canonical) Filter.atTop Filter.atTop :=
  frontier_tendsto_atTop canonical

theorem multipleFrontier_eventually_gt (s : GreedySeq) (q : ℕ)
    (hqpos : 0 < q) (B : ℕ) :
    ∃ T, ∀ t, T ≤ t → B < multipleFrontier s q hqpos t := by
  obtain ⟨T, hT⟩ := finite_positive_interval_eventually_used s B
  refine ⟨T, ?_⟩
  intro t ht
  by_contra h
  have hp := multipleFrontier_spec s q hqpos t
  exact hp.2.2 (hT t ht _ hp.1 (by omega))

theorem multipleFrontier_tendsto_atTop (s : GreedySeq) (q : ℕ) (hqpos : 0 < q) :
    Filter.Tendsto (multipleFrontier s q hqpos) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro B
  obtain ⟨T, hT⟩ := multipleFrontier_eventually_gt s q hqpos B
  exact ⟨T, fun t ht => (hT t ht).le⟩

namespace Clock

noncomputable def usedValues (s : GreedySeq) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (t+1)).image s.a

theorem mem_usedValues (s : GreedySeq) (t m : ℕ) :
    m ∈ usedValues s t ↔ UsedBefore s.a (t+1) m := by
  classical
  simp only [usedValues, Finset.mem_image, Finset.mem_range, UsedBefore]

theorem usedValues_card (s : GreedySeq) (t : ℕ) :
    (usedValues s t).card = t+1 := by
  classical
  rw [usedValues, Finset.card_image_of_injective _ s.injective, Finset.card_range]

theorem usedValues_positive (s : GreedySeq) {t m : ℕ} (hm : m ∈ usedValues s t) :
    0 < m := by
  obtain ⟨i, _, hi⟩ := (mem_usedValues s t m).mp hm
  exact hi ▸ s.positive i

theorem frontier_not_mem_usedValues (s : GreedySeq) (t : ℕ) :
    frontier s t ∉ usedValues s t := by
  intro hm
  exact (frontier_spec s t).2.2 ((mem_usedValues s t _).mp hm)

noncomputable def usedBelow (s : GreedySeq) (t : ℕ) : Finset ℕ := by
  classical
  exact (usedValues s t).filter (fun m => m < frontier s t)

noncomputable def usedAbove (s : GreedySeq) (t : ℕ) : Finset ℕ := by
  classical
  exact (usedValues s t).filter (fun m => frontier s t < m)

noncomputable def missingBelow (s : GreedySeq) (t : ℕ) : Finset ℕ := by
  classical
  exact Finset.Ico 1 (frontier s t) \ usedValues s t

noncomputable def oddAbove (s : GreedySeq) (t : ℕ) : Finset ℕ := by
  classical
  exact (usedValues s t).filter (fun m => ¬ 2 ∣ m ∧ frontier s t < m)

noncomputable def missingPrimes (s : GreedySeq) (t : ℕ) : Finset ℕ := by
  classical
  exact (missingBelow s t).filter Nat.Prime

noncomputable def holes (s : GreedySeq) (t : ℕ) : Finset ℕ := by
  classical
  exact (missingBelow s t).filter (fun m => ¬ m.Prime)

noncomputable def tickAbove (s : GreedySeq) (t : ℕ) (tick : ℕ → Prop) : Finset ℕ := by
  classical
  exact (oddAbove s t).filter tick

noncomputable def nonTickOddAbove (s : GreedySeq) (t : ℕ)
    (tick : ℕ → Prop) : Finset ℕ := by
  classical
  exact (oddAbove s t).filter (fun m => ¬ tick m)

/-- Every positive even below the frontier belongs to the finite prefix. -/
theorem smaller_even_mem_usedValues (s : GreedySeq) {t m : ℕ}
    (hm : 0 < m) (heven : 2 ∣ m) (hlt : m < frontier s t) :
    m ∈ usedValues s t :=
  (mem_usedValues s t m).mpr (smaller_even_used s hm heven hlt)

/-- Finite injectivity alone gives a linear upper bound for the frontier. -/
theorem frontier_le_twice_time_add_two (s : GreedySeq) (t : ℕ) :
    frontier s t ≤ 2*(t+2) := by
  classical
  have hc : (Finset.Ico 1 (frontier s t / 2)).card ≤ (usedValues s t).card := by
    apply Finset.card_le_card_of_injOn (fun k : ℕ => 2*k)
    · intro k hk
      have hk' := Finset.mem_Ico.mp hk
      change 2*k ∈ usedValues s t
      exact smaller_even_mem_usedValues s (by omega) ⟨k, rfl⟩ (by omega)
    · intro i _ j _ hij
      dsimp at hij
      omega
  rw [Nat.card_Ico, usedValues_card] at hc
  obtain ⟨k, hk⟩ := (frontier_spec s t).2.1
  omega

/-- The missing integers below the frontier are odd and exceed one. -/
theorem missingBelow_spec (s : GreedySeq) {t m : ℕ} (hm : m ∈ missingBelow s t) :
    1 < m ∧ m < frontier s t ∧ ¬ 2 ∣ m ∧ ¬ UsedBefore s.a (t+1) m := by
  classical
  obtain ⟨hinterval, hfree⟩ := Finset.mem_sdiff.mp hm
  obtain ⟨hpos, hlt⟩ := Finset.mem_Ico.mp hinterval
  have hnot : ¬ UsedBefore s.a (t+1) m :=
    fun hu => hfree ((mem_usedValues s t m).mpr hu)
  have hne : m ≠ 1 := by
    intro he
    apply hnot
    exact ⟨0, by omega, s.seed_zero.trans he.symm⟩
  refine ⟨by omega, hlt, ?_, hnot⟩
  intro heven
  exact hnot (smaller_even_used s (by omega) heven hlt)

theorem holes_spec (s : GreedySeq) {t m : ℕ} (hm : m ∈ holes s t) :
    1 < m ∧ ¬ m.Prime ∧ ¬ 2 ∣ m ∧ m < frontier s t ∧
      ¬ UsedBefore s.a (t+1) m := by
  classical
  obtain ⟨hmissing, hnp⟩ := Finset.mem_filter.mp hm
  have hs := missingBelow_spec s hmissing
  exact ⟨hs.1, hnp, hs.2.2.1, hs.2.1, hs.2.2.2⟩

theorem used_below_above_card (s : GreedySeq) (t : ℕ) :
    (usedBelow s t).card + (usedAbove s t).card = t+1 := by
  classical
  have hfilter : (usedValues s t).filter (fun m => ¬ m < frontier s t) =
      usedAbove s t := by
    ext m
    simp only [usedAbove, Finset.mem_filter]
    constructor
    · rintro ⟨hm, hge⟩
      have hne : m ≠ frontier s t := by
        intro he
        exact frontier_not_mem_usedValues s t (he ▸ hm)
      exact ⟨hm, by omega⟩
    · rintro ⟨hm, hgt⟩
      exact ⟨hm, by omega⟩
  have hc := Finset.card_filter_add_card_filter_not (s := usedValues s t)
    (fun m => m < frontier s t)
  rw [hfilter, usedValues_card] at hc
  exact hc

theorem used_below_missing_card (s : GreedySeq) (t : ℕ) :
    (usedBelow s t).card + (missingBelow s t).card = frontier s t - 1 := by
  classical
  have heq : usedBelow s t = Finset.Ico 1 (frontier s t) ∩ usedValues s t := by
    ext m
    simp only [usedBelow, Finset.mem_filter, Finset.mem_inter, Finset.mem_Ico]
    constructor
    · rintro ⟨hm, hlt⟩
      exact ⟨⟨usedValues_positive s hm, hlt⟩, hm⟩
    · rintro ⟨⟨_, hlt⟩, hm⟩
      exact ⟨hm, hlt⟩
  have hc := Finset.card_sdiff_add_card_inter (Finset.Ico 1 (frontier s t))
    (usedValues s t)
  rw [← heq, Nat.card_Ico] at hc
  change (missingBelow s t).card + (usedBelow s t).card = frontier s t - 1 at hc
  omega

theorem even_odd_above_card (s : GreedySeq) (t : ℕ) :
    earlyEvenCount s t + (oddAbove s t).card = (usedAbove s t).card := by
  classical
  have heq : (usedAbove s t).filter (fun m => 2 ∣ m) =
      (usedValues s t).filter (fun m => 2 ∣ m ∧ frontier s t < m) := by
    ext m
    simp only [usedAbove, Finset.mem_filter]
    tauto
  have hoq : (usedAbove s t).filter (fun m => ¬ 2 ∣ m) = oddAbove s t := by
    ext m
    simp only [usedAbove, oddAbove, Finset.mem_filter]
    tauto
  have hc := Finset.card_filter_add_card_filter_not (s := usedAbove s t) (fun m => 2 ∣ m)
  rw [heq, hoq] at hc
  exact hc

theorem missing_prime_holes_card (s : GreedySeq) (t : ℕ) :
    (missingPrimes s t).card + (holes s t).card = (missingBelow s t).card := by
  classical
  exact Finset.card_filter_add_card_filter_not (s := missingBelow s t) Nat.Prime

theorem tick_nontick_odd_above_card (s : GreedySeq) (t : ℕ) (tick : ℕ → Prop) :
    (tickAbove s t tick).card + (nonTickOddAbove s t tick).card = (oddAbove s t).card := by
  classical
  exact Finset.card_filter_add_card_filter_not (s := oddAbove s t) tick

/-- Exact natural-number clock balance, without truncated subtraction. -/
theorem clock_balance (s : GreedySeq) (t : ℕ) :
    t+1 + (missingBelow s t).card + 1 =
      frontier s t + earlyEvenCount s t + (oddAbove s t).card := by
  have hused := used_below_above_card s t
  have hmissing := used_below_missing_card s t
  have habove := even_odd_above_card s t
  have hp := (frontier_spec s t).1
  omega

/-- The signed time/frontier identity valid for every actual EKG prefix. -/
theorem clock_identity (s : GreedySeq) (t : ℕ) :
    (frontier s t : ℤ) - ((t+1 : ℕ) : ℤ) =
      1 + ((missingBelow s t).card : ℤ) - (earlyEvenCount s t : ℤ) -
        ((oddAbove s t).card : ℤ) := by
  have h := clock_balance s t
  omega

theorem clock_identity_prime_holes (s : GreedySeq) (t : ℕ) :
    (frontier s t : ℤ) - ((t+1 : ℕ) : ℤ) =
      1 + ((missingPrimes s t).card : ℤ) + ((holes s t).card : ℤ) -
        (earlyEvenCount s t : ℤ) - ((oddAbove s t).card : ℤ) := by
  have h := clock_identity s t
  have hp := missing_prime_holes_card s t
  omega

/-- The tick predicate is arbitrary; defining this partition asserts no
prime-neighbor pattern. -/
theorem clock_identity_with_ticks (s : GreedySeq) (t : ℕ) (tick : ℕ → Prop) :
    (frontier s t : ℤ) - ((t+1 : ℕ) : ℤ) =
      1 + ((missingPrimes s t).card : ℤ) - ((tickAbove s t tick).card : ℤ) +
        ((holes s t).card : ℤ) - (earlyEvenCount s t : ℤ) -
        ((nonTickOddAbove s t tick).card : ℤ) := by
  have h := clock_identity_prime_holes s t
  have ht := tick_nontick_odd_above_card s t tick
  omega

/-- Modular transfer to the manuscript interval counts. The two exact
cardinal identities, including endpoint errors, are explicit hypotheses. -/
theorem clock_identity_from_interval_counts (s : GreedySeq) (t : ℕ)
    (tick : ℕ → Prop) (primeInterval tickInterval primeError tickError : ℕ)
    (hprime : (missingPrimes s t).card = primeInterval + primeError)
    (htick : (tickAbove s t tick).card + tickError = tickInterval) :
    (frontier s t : ℤ) - ((t+1 : ℕ) : ℤ) =
      1 + (primeInterval : ℤ) - (tickInterval : ℤ) + ((holes s t).card : ℤ) -
        (earlyEvenCount s t : ℤ) - ((nonTickOddAbove s t tick).card : ℤ) +
        ((primeError + tickError : ℕ) : ℤ) := by
  have h := clock_identity_with_ticks s t tick
  omega

/-- All missing primes are among the primes at most the frontier. No
prime-introduction pattern is needed for this upper bound. -/
theorem missingPrimes_card_le_primeCounting (s : GreedySeq) (t : ℕ) :
    (missingPrimes s t).card ≤ Nat.primeCounting (frontier s t) := by
  classical
  calc
    (missingPrimes s t).card ≤ ((frontier s t + 1).primesBelow).card := by
      apply Finset.card_le_card
      intro m hm
      obtain ⟨hmissing, hp⟩ := Finset.mem_filter.mp hm
      have hs := missingBelow_spec s hmissing
      exact Nat.mem_primesBelow.mpr ⟨by omega, hp⟩
    _ = Nat.primeCounting (frontier s t) := by
      rw [Nat.primesBelow_card_eq_primeCounting']
      rfl

/-- Distinct odd non-tick values in `(E, Top]` are bounded in number by
the full integer span; the bound also covers an empty interval. -/
theorem nonTickOddAbove_card_le_span (s : GreedySeq) (t : ℕ)
    (tick : ℕ → Prop) (Top : ℕ)
    (hTop : ∀ m ∈ nonTickOddAbove s t tick, m ≤ Top) :
    (nonTickOddAbove s t tick).card ≤ Top - frontier s t := by
  classical
  calc
    (nonTickOddAbove s t tick).card ≤ (Finset.Ioc (frontier s t) Top).card := by
      apply Finset.card_le_card
      intro m hm
      have hodd := (Finset.mem_filter.mp hm).1
      have hhigh := (Finset.mem_filter.mp hodd).2.2
      exact Finset.mem_Ioc.mpr ⟨hhigh, hTop m hm⟩
    _ = Top - frontier s t := Nat.card_Ioc (frontier s t) Top

/-- A direct absolute-error bound suitable for big-O assembly. -/
theorem clock_abs_le_counts (s : GreedySeq) (t : ℕ) (tick : ℕ → Prop) :
    |(frontier s t : ℤ) - ((t+1 : ℕ) : ℤ)| ≤
      1 + ((missingPrimes s t).card : ℤ) + ((holes s t).card : ℤ) +
        (earlyEvenCount s t : ℤ) + ((tickAbove s t tick).card : ℤ) +
        ((nonTickOddAbove s t tick).card : ℤ) := by
  have h := clock_identity_with_ticks s t tick
  apply abs_le.mpr
  constructor <;> omega

/-- Analytic assembly needs only the supplied tick cardinal bound, together
with the unconditional missing-prime bound and a non-tick upper cutoff. -/
theorem clock_abs_le_prime_and_span (s : GreedySeq) (t : ℕ)
    (tick : ℕ → Prop) (Top : ℕ)
    (hTick : (tickAbove s t tick).card ≤ Nat.primeCounting (frontier s t))
    (hTop : ∀ m ∈ nonTickOddAbove s t tick, m ≤ Top) :
    |(frontier s t : ℤ) - ((t+1 : ℕ) : ℤ)| ≤
      1 + 2 * (Nat.primeCounting (frontier s t) : ℤ) + ((holes s t).card : ℤ) +
        (earlyEvenCount s t : ℤ) + ((Top - frontier s t : ℕ) : ℤ) := by
  have h := clock_abs_le_counts s t tick
  have hp := missingPrimes_card_le_primeCounting s t
  have hspan := nonTickOddAbove_card_le_span s t tick Top hTop
  omega

end Clock
end EKG
