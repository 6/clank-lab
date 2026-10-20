import EKG.PrimeStructureObstruction
import EKG.PrimePatternBase
import EKG.PatternCount

/-! The global EKG 2p,p,3p structure theorem. The sequence's finite base is
kernel-checked. The bounded numerical inequality currently uses the
native_decide trust extension in PatternCount; the unbounded range uses
the proved modulus-210 sieve. The audit module exposes this dependency. -/
namespace EKG

theorem primeIntroductionPattern (s : GreedySeq) : PrimeIntroductionPattern s := by
  have hall : ∀ p n, NewPrimeAt s n p → p ≠ 2 → s.a n = 2*p := by
    intro p
    induction p using Nat.strong_induction_on with
    | h p ih =>
      intro n hnew hp2
      by_cases hp43 : p ≤ 43
      · exact PrimePatternBase.firstMultiple_eq_twice s hnew hp43 hp2
      by_contra hbad
      have hobs := bad_introduction_count_obstruction s hnew hp2 hbad
        (fun m r hr hnewr hr2 => ih r hr m hnewr hr2)
      have hcount : Nat.primeCounting (Nat.sqrt (2*p)) +
          (Nat.primeCounting (p-1) - Nat.primeCounting (2*p/3)) <
          (p-1)/2 - p/3 + 1 := by
        by_cases hp4096 : 4096 ≤ p
        · exact primeStructure_large_count hp4096
        · exact PatternCount.finite_inequality hnew.1 (by omega) (by omega)
      omega
  exact fun n p hnew hp2 => hall p n hnew hp2

theorem firstMultiple_eq_twice (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) : s.a n = 2*p :=
  primeIntroductionPattern s n p h hp2

theorem firstMultiple_predecessor_even (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) : 2 ∣ s.a (n-1) :=
  (firstMultiple_eq_twice_iff_even_predecessor s h hp2).mp
    (firstMultiple_eq_twice s h hp2)

theorem firstMultiple_triple (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) :
    s.a n = 2*p ∧ s.a (n+1) = p ∧ s.a (n+2) = 3*p := by
  have he := firstMultiple_eq_twice s h hp2
  exact ⟨he, firstMultiple_next_prime s h hp2,
    firstMultiple_next_three_of_twice s h hp2 he⟩

theorem firstMultiple_frontier (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) : frontier s (n-1) = 2*p :=
  firstMultiple_frontier_of_twice s h hp2 (firstMultiple_eq_twice s h hp2)

theorem odd_prime_triple_exists (s : GreedySeq) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ n, NewPrimeAt s n p ∧ s.a n = 2*p ∧
      s.a (n+1) = p ∧ s.a (n+2) = 3*p := by
  obtain ⟨n, hn⟩ := every_prime_introduced s hp
  exact ⟨n, hn, firstMultiple_triple s hn hp2⟩

theorem prime_occurrence_block (s : GreedySeq) {i p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (heq : s.a i = p) :
    3 ≤ i ∧ s.a (i-1) = 2*p ∧ s.a (i+1) = 3*p ∧
      frontier s (i-2) = 2*p := by
  obtain ⟨hi, hnew⟩ := primeOccurrenceIntro s hp hp2 heq
  have htriple := firstMultiple_triple s hnew hp2
  have he : i-1+2 = i+1 := by omega
  have hf : i-1-1 = i-2 := by omega
  exact ⟨hi, htriple.1, by simpa [he] using htriple.2.2,
    by simpa [hf] using firstMultiple_frontier s hnew hp2⟩

theorem odd_prime_tick_unique (s : GreedySeq) {i p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (heq : s.a i = 3*p) :
    ∃ n, NewPrimeAt s n p ∧ i = n+2 ∧ s.a (i-1) = p := by
  obtain ⟨n, hn⟩ := every_prime_introduced s hp
  have htriple := firstMultiple_triple s hn hp2
  have hi : i = n+2 := s.injective (heq.trans htriple.2.2.symm)
  exact ⟨n, hn, hi, by simpa [hi] using htriple.2.1⟩

theorem primeStructure_odd_not_two_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ 2 ∣ p := by
  intro hd
  rcases (Nat.dvd_prime hp).mp hd with he | he
  · omega
  · exact hp2 he.symm

theorem primeStructure_tick_not_two_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ 2 ∣ 3*p := by
  intro hd
  rcases Nat.prime_two.dvd_mul.mp hd with h3 | hpdiv
  · exact (by decide : ¬ 2 ∣ 3) h3
  · exact primeStructure_odd_not_two_dvd hp hp2 hpdiv

theorem prime_introductions_separated (s : GreedySeq) {n m p r : ℕ}
    (hp : NewPrimeAt s n p) (hp2 : p ≠ 2)
    (hr : NewPrimeAt s m r) (hr2 : r ≠ 2) (hnm : n < m) : n+4 ≤ m := by
  have htriple := firstMultiple_triple s hp hp2
  have hmeven : 2 ∣ s.a m := by
    rw [firstMultiple_eq_twice s hr hr2]
    exact Nat.dvd_mul_right 2 r
  have hmprev := firstMultiple_predecessor_even s hr hr2
  by_contra hnot
  have hc : m = n+1 ∨ m = n+2 ∨ m = n+3 := by omega
  rcases hc with hc | hc | hc
  · rw [hc, htriple.2.1] at hmeven
    exact primeStructure_odd_not_two_dvd hp.1 hp2 hmeven
  · rw [hc, htriple.2.2] at hmeven
    exact primeStructure_tick_not_two_dvd hp.1 hp2 hmeven
  · have he : m-1 = n+2 := by omega
    rw [he, htriple.2.2] at hmprev
    exact primeStructure_tick_not_two_dvd hp.1 hp2 hmprev

theorem prime_introduction_before_frontier (s : GreedySeq) {n p t : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) (hnt : n ≤ t) : 2*p < frontier s t := by
  have hle := frontier_monotone s (show n-1 ≤ t by omega)
  rw [firstMultiple_frontier s h hp2] at hle
  have hne := frontier_ne_used s hnt
  rw [firstMultiple_eq_twice s h hp2] at hne
  omega

theorem used_tick_prime_below_frontier (s : GreedySeq) {i p t : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (heq : s.a i = 3*p) (hit : i ≤ t) :
    2*p < frontier s t := by
  obtain ⟨n, hn, hi, _⟩ := odd_prime_tick_unique s hp hp2 heq
  exact prime_introduction_before_frontier s hn hp2 (by omega)

theorem multipleFrontier_after_tick (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) :
    multipleFrontier s p h.1.pos (n+2) = 4*p := by
  change leastUnusedMultiple s (n+2) p h.1.pos = 4*p
  exact leastUnusedMultiple_after_tick s h hp2 (firstMultiple_eq_twice s h hp2)

end EKG
