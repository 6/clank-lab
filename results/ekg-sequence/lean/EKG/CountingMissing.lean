import EKG.CountingOccurrences
import EKG.CountingPrimeIntervals

/-! Missing primes are the frozen half interval together with the prime
introduced at the final observed index, if there is one. -/
namespace EKG.CanonicalCounting

noncomputable def finalIntroductionPrimes (u : ℕ) : Finset ℕ := by
  classical
  exact ((e u).primesBelow).filter (fun p =>
    p ≠ 2 ∧ 2*p < e u ∧ NewPrimeAt canonical u p)

theorem missingPrimes_mem_iff {u p : ℕ} :
    p ∈ Clock.missingPrimes canonical u ↔
      p.Prime ∧ p < e u ∧ ¬ UsedBefore canonical.a (u+1) p := by
  classical
  simp only [Clock.missingPrimes, Clock.missingBelow, Finset.mem_filter,
    Finset.mem_sdiff, Finset.mem_Ico, Clock.mem_usedValues]
  constructor
  · rintro ⟨⟨⟨_, hlt⟩, hfree⟩, hp⟩
    exact ⟨hp, hlt, hfree⟩
  · rintro ⟨hp, hlt, hfree⟩
    exact ⟨⟨⟨by have := hp.two_le; omega, hlt⟩, hfree⟩, hp⟩

theorem missingPrimes_eq_union (u : ℕ) (hu : 8 ≤ u) :
    Clock.missingPrimes canonical u = P1 u ∪ finalIntroductionPrimes u := by
  classical
  ext p
  rw [missingPrimes_mem_iff, Finset.mem_union]
  constructor
  · rintro ⟨hp, hbelow, hfree⟩
    have hp2 : p ≠ 2 := by
      intro h
      apply hfree
      exact ⟨1, by omega, canonical.seed_one.trans h.symm⟩
    by_cases hhalf : e u ≤ 2*p
    · exact Or.inl (Finset.mem_filter.mpr
        ⟨Nat.mem_primesBelow.mpr ⟨hbelow, hp⟩, hhalf⟩)
    · obtain ⟨n, hn⟩ := every_prime_introduced canonical hp
      have hnu : n ≤ u :=
        (introduction_le_iff_twice_lt_frontier hn hp2).mpr
          (show 2*p < e u by omega)
      have hnfinal : n = u := by
        have hnot : ¬ n+1 ≤ u := by
          intro h
          exact hfree ((prime_used_iff hn hp2).mpr h)
        omega
      exact Or.inr (Finset.mem_filter.mpr
        ⟨Nat.mem_primesBelow.mpr ⟨hbelow, hp⟩,
          hp2, by omega, hnfinal ▸ hn⟩)
  · intro h
    rcases h with hp1 | hfinal
    · obtain ⟨hmem, hhalf⟩ := Finset.mem_filter.mp hp1
      obtain ⟨hbelow, hp⟩ := Nat.mem_primesBelow.mp hmem
      have he := counting_frontier_ge_fourteen hu
      have hp2 : p ≠ 2 := by intro h; subst p; omega
      refine ⟨hp, hbelow, ?_⟩
      intro hused
      obtain ⟨n, hn⟩ := every_prime_introduced canonical hp
      have hnused := (prime_used_iff hn hp2).mp hused
      have hsmall : 2*p < e u :=
        introduction_before_frontier hn hp2 (show n ≤ u by omega)
      omega
    · obtain ⟨hmem, hp2, hhalf, hnew⟩ := Finset.mem_filter.mp hfinal
      obtain ⟨hbelow, hp⟩ := Nat.mem_primesBelow.mp hmem
      refine ⟨hp, hbelow, ?_⟩
      rw [prime_used_iff hnew hp2]
      omega

theorem finalIntroductionPrimes_card (u : ℕ) :
    (finalIntroductionPrimes u).card = theta1 u := by
  classical
  unfold theta1
  split_ifs with hex
  · obtain ⟨p, hp, hp2, hhalf, hnew⟩ := hex
    have hmem : p ∈ finalIntroductionPrimes u := Finset.mem_filter.mpr
      ⟨Nat.mem_primesBelow.mpr ⟨by have := hp.pos; omega, hp⟩, hp2, hhalf, hnew⟩
    apply Finset.card_eq_one.mpr
    refine ⟨p, Finset.ext fun q => ?_⟩
    constructor
    · intro hq
      obtain ⟨_, hq2, _, hqnew⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_singleton.mpr (introduction_prime_unique hqnew hq2 hnew hp2)
    · intro hq
      simpa only [Finset.mem_singleton.mp hq] using hmem
  · have hempty : finalIntroductionPrimes u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hmem
      obtain ⟨hp, hp2, hhalf, hnew⟩ := Finset.mem_filter.mp hmem
      exact hex ⟨p, (Nat.mem_primesBelow.mp hp).2, hp2, hhalf, hnew⟩
    rw [hempty, Finset.card_empty]

theorem missingPrimes_card (u : ℕ) (hu : 8 ≤ u) :
    (Clock.missingPrimes canonical u).card = (P1 u).card + theta1 u := by
  classical
  rw [missingPrimes_eq_union u hu, Finset.card_union_of_disjoint,
    finalIntroductionPrimes_card]
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hge := (Finset.mem_filter.mp hp).2
  have hlt := (Finset.mem_filter.mp hq).2.2.1
  omega

end EKG.CanonicalCounting
