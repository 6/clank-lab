import EKG.SelfPairing
import EKG.PrimeStructureLocal
import EKG.FiniteBase

namespace EKG

theorem frontier_ge_fourteen (s : GreedySeq) {t : ℕ} (ht : 8 ≤ t) :
    14 ≤ frontier s t := by
  have h := frontier_monotone s ht
  rw [FiniteBase.frontier_eq s (t := 8) (by omega)] at h
  exact h

theorem prime_up_at_least_five (s : GreedySeq) {t i : ℕ} (ht : 8 ≤ t)
    (hi : i ∈ primeUps s t) : 5 ≤ s.a i := by
  classical
  obtain ⟨_, hp, _, hu⟩ := Finset.mem_filter.mp hi
  have he := frontier_ge_fourteen s ht
  have hp2 := hp.two_le
  by_contra h
  have hc : s.a i = 2 ∨ s.a i = 3 ∨ s.a i = 4 := by omega
  rcases hc with hc | hc | hc
  · have hi1 : i = 1 := s.injective (hc.trans s.seed_one.symm)
    have hv : s.a 2 = 4 := FiniteBase.first_thirteen s (by omega)
    rw [hi1] at hu
    change frontier s t ≤ s.a 2 at hu
    omega
  · have hv : s.a 4 = 3 := FiniteBase.first_thirteen s (by omega)
    have hi4 : i = 4 := s.injective (hc.trans hv.symm)
    have hv' : s.a 5 = 9 := FiniteBase.first_thirteen s (by omega)
    rw [hi4] at hu
    change frontier s t ≤ s.a 5 at hu
    omega
  · rw [hc] at hp
    exact (by decide : ¬ Nat.Prime 4) hp

/-- A prime occurrence is precisely the successor of its first introduction.
This statement uses no assumption about the multiplier of that introduction. -/
theorem prime_occurrence_backlink (s : GreedySeq) {i p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (heq : s.a i = p) :
    3 ≤ i ∧ NewPrimeAt s (i-1) p := by
  obtain ⟨n, hn⟩ := every_prime_introduced s hp
  have hi : n+1 = i := s.injective ((firstMultiple_next_prime s hn hp2).trans heq.symm)
  have hni := newPrime_index s hn hp2
  have hback : i-1 = n := by omega
  exact ⟨by omega, by rwa [hback]⟩

/-- Explicit structural interface, not an axiom. It is discharged using
`primeIntroductionPattern` in `EKG.VerifiedCounts`. -/
def PrimePatternForCounts (s : GreedySeq) : Prop :=
  ∀ n p, NewPrimeAt s n p → p ≠ 2 → s.a n = 2*p

/-- Lemma EE with an explicit structural input. `EKG.VerifiedCounts` supplies
the proved pattern and exports the unconditional recurrence and bound. -/
theorem early_even_recurrence_of_prime_pattern (s : GreedySeq)
    (hpattern : PrimePatternForCounts s) {t : ℕ} (ht : 10 ≤ t) :
    earlyEvenCount s t ≤ Nat.primeCounting (Nat.sqrt (frontier s t)) +
      6 + 48 * ((4 * priorPeak (earlyEvenCount s) t + 3) / 210 + 1) := by
  classical
  let Q := unpairedPrimeUps s t
  let R := Q.filter (fun i => i+1 < t)
  let K := priorPeak (earlyEvenCount s) t
  have hprime : ∀ i ∈ R, (s.a i).Prime := by
    intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).1).1).2.1
  have hnear : ∀ i ∈ R, 2*s.a i < frontier s t ∧
      frontier s t < 2*s.a i + 8*K + 8 := by
    intro i hi
    obtain ⟨hQ, hit⟩ := Finset.mem_filter.mp hi
    have hup := (Finset.mem_sdiff.mp hQ).1
    have hp := (Finset.mem_filter.mp hup).2.1
    have hp5 := prime_up_at_least_five s (by omega) hup
    have hp2 : s.a i ≠ 2 := by omega
    obtain ⟨hii, hnew⟩ := prime_occurrence_backlink s hp hp2 rfl
    have hfirst := hpattern (i-1) (s.a i) hnew hp2
    have htick := firstMultiple_next_three_of_twice s hnew hp2 hfirst
    have hbefore := firstMultiple_frontier_of_twice s hnew hp2 hfirst
    have h1 : i-1+2 = i+1 := by omega
    have h2 : i-1-1 = i-2 := by omega
    have hodd : ¬ 2 ∣ 3*s.a i := by
      apply Nat.prime_two.not_dvd_mul (by decide : ¬ 2 ∣ 3)
      intro hd
      exact hp2 ((hp.dvd_iff_eq (by omega : 2 ≠ 1)).mp hd)
    apply unpaired_tick_near_frontier s hQ hit hii rfl hfirst
      (by rwa [h1] at htick) hodd (by rwa [h2] at hbefore)
  have hRcard := nearby_prime_family_bound s (frontier s t) K R
    (frontier_spec s t).2.1 hprime hnear
  have hQcard : Q.card ≤ R.card+1 := by
    have hsub : Q ⊆ insert (t-1) R := by
      intro i hi
      by_cases hit : i+1 < t
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hi, hit⟩))
      · have hir := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).1
        have hi' : i = t-1 := by have := Finset.mem_range.mp hir; omega
        exact Finset.mem_insert.mpr (Or.inl hi')
    have hc := Finset.card_le_card hsub
    have hd := Finset.card_insert_le (t-1) R
    omega
  have hcancel := earlyEvenCount_le_unpaired s t (by omega)
  dsimp [Q, K] at *
  omega

theorem early_even_bound_of_prime_pattern
    (hpattern : PrimePatternForCounts canonical) : ∀ t,
    earlyEvenCount canonical t ≤
      12 * Nat.primeCounting (Nat.sqrt (frontier canonical t)) + 720 := by
  apply bootstrap_from_counting_recurrence
  · exact frontier_prime_count_monotone canonical
  · exact FiniteBase.earlyEvenBase
  · intro t ht
    exact early_even_recurrence_of_prime_pattern canonical hpattern ht

end EKG
