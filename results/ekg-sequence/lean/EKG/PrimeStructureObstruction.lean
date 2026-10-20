import EKG.PrimeStructureLocal
import EKG.PrimeStructurePermutation
import EKG.CrossingBounds
import EKG.PrimeStructureLarge

namespace EKG

/-- The global structural input, with the seed prime 2 explicitly excluded. -/
def PrimeIntroductionPattern (s : GreedySeq) : Prop :=
  ∀ n p, NewPrimeAt s n p → p ≠ 2 → s.a n = 2*p

theorem primeStructure_term_two (s : GreedySeq) : s.a 2 = 4 := by
  have hfree : ¬ UsedBefore s.a 2 (2*2) := by
    rintro ⟨i, hi, he⟩
    have hc : i = 0 ∨ i = 1 := by omega
    rcases hc with hc | hc <;> subst i
    · rw [s.seed_zero] at he; omega
    · rw [s.seed_one] at he; omega
  have hsmall : ∀ j, 0 < j → j < 2 → UsedBefore s.a 2 (j*2) := by
    intro j hj hj2
    have : j = 1 := by omega
    subst j
    exact ⟨1, by omega, by simpa using s.seed_one⟩
  exact after_prime_eq_multiple s (t := 1) (by omega) Nat.prime_two
    s.seed_one (by omega : 0 < 2) hfree hsmall

/-- Under the induction hypothesis for smaller primes, every prime-base
upcrossing of 2p is a tick r -> 3r with 2p/3 < r < p. -/
theorem prime_upcrossing_before_introduction (s : GreedySeq) {n p i : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2)
    (ih : ∀ m r, r < p → NewPrimeAt s m r → r ≠ 2 → s.a m = 2*r)
    (hi : i < n) (hprime : (s.a i).Prime)
    (hcross : s.a i < 2*p ∧ 2*p ≤ s.a (i+1)) :
    2*p/3 < s.a i ∧ s.a i < p := by
  have hp3 : 3 ≤ p := by have := h.1.two_le; omega
  have hrp : s.a i < p := prior_prime_lt s h hp2 hi hprime (dvd_refl _)
  have hr2 : s.a i ≠ 2 := by
    intro he
    have hii : i = 1 := s.injective (he.trans s.seed_one.symm)
    have hnext := primeStructure_term_two s
    rw [hii, hnext] at hcross
    omega
  obtain ⟨hi3, hnew⟩ := primeOccurrenceIntro s hprime hr2 rfl
  have heq := ih (i-1) (s.a i) hrp hnew hr2
  have htick := firstMultiple_next_three_of_twice s hnew hr2 heq
  have he : i-1+2 = i+1 := by omega
  rw [he] at htick
  have hlt : 2*p < 3*s.a i := by
    by_cases hii : i+1 < n
    · have hne : s.a (i+1) ≠ 2*p := by
        intro he'
        apply h.2.2 (i+1) hii
        rw [he']
        exact Nat.dvd_mul_left p 2
      rw [htick] at hcross hne
      omega
    · have hii : i+1 = n := by omega
      have hnewdiv := h.2.1
      rw [← hii, htick] at hnewdiv
      rcases h.1.dvd_mul.mp hnewdiv with hpdiv | hpdiv
      · have := Nat.le_of_dvd (by omega : 0 < 3) hpdiv
        have : p = 3 := by omega
        have := hprime.two_le
        omega
      · have := Nat.le_of_dvd (s.positive i) hpdiv
        omega
  exact ⟨by omega, hrp⟩

/-- Actual crossing obstruction for a bad first introduction. The only
induction hypothesis concerns smaller primes. No crossing counts or greedy
properties are postulated. -/
theorem bad_introduction_count_obstruction (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) (hbad : s.a n ≠ 2*p)
    (ih : ∀ m r, r < p → NewPrimeAt s m r → r ≠ 2 → s.a m = 2*r) :
    (p-1)/2 - p/3 + 1 ≤ Nat.primeCounting (Nat.sqrt (2*p)) +
      (Nat.primeCounting (p-1) - Nat.primeCounting (2*p/3)) := by
  classical
  obtain ⟨q, hq, hqb, heq, _⟩ := firstMultiple_eq_mul s h hp2
  have hn := newPrime_index s h hp2
  have hp0 := h.1.pos
  have hp3 : 3 ≤ p := by have := h.1.two_le; omega
  have hq3 : 3 ≤ q := by
    have hq2 := hq.two_le
    by_contra hnot
    have : q = 2 := by omega
    exact hbad (by simpa [this] using heq)
  have hbig : 2*p < s.a n := by rw [heq]; nlinarith
  let J := Finset.Ioc (p/3) ((p-1)/2)
  let D := (Finset.range n).filter (fun i => 2*p ≤ s.a i ∧ s.a (i+1) < 2*p)
  have hused : ∀ j ∈ J, ∃ i < n, s.a i = 2*q*j := by
    intro j hj
    obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ioc.mp hj
    have hj0 : 0 < j := by omega
    have h2j : 2*j < p := by omega
    have hu := lower_multiple_used s h hp2 hq hqb heq (by omega : 0 < 2*j) h2j
    simpa [UsedBefore, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hu
  let pos : ℕ → ℕ := fun j => if hj : j ∈ J then Classical.choose (hused j hj) else 0
  have hpos : ∀ j (hj : j ∈ J), pos j < n ∧ s.a (pos j) = 2*q*j := by
    intro j hj
    simp only [pos, dif_pos hj]
    exact Classical.choose_spec (hused j hj)
  have hJle : J.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn pos
    · intro j hj
      have hv := hpos j hj
      obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ioc.mp hj
      have h3j : p < 3*j := by omega
      have hqj : 3*j ≤ q*j := Nat.mul_le_mul_right j hq3
      have habove : 2*p < s.a (pos j) := by rw [hv.2]; nlinarith
      have hi1 : 1 ≤ pos j := by
        by_contra hnot
        have hz : pos j = 0 := by omega
        rw [hz, s.seed_zero] at habove
        omega
      have hfree : ¬ UsedBefore s.a (pos j+1) (2*p) := by
        rintro ⟨i, hi, hei⟩
        apply h.2.2 i (by omega)
        rw [hei]
        exact Nat.dvd_mul_left p 2
      have hnext : s.a (pos j+1) ≤ 2*p := by
        apply s.minimal (pos j+1) (by omega) (2*p) (by omega) hfree
        have he : pos j+1-1 = pos j := by omega
        rw [he, hv.2]
        exact ⟨2, Nat.prime_two, ⟨q*j, by ring⟩, Nat.dvd_mul_right 2 p⟩
      have hne : s.a (pos j+1) ≠ 2*p := by
        intro he
        by_cases hil : pos j+1 < n
        · apply h.2.2 (pos j+1) hil
          rw [he]
          exact Nat.dvd_mul_left p 2
        · have hie : pos j+1 = n := by omega
          rw [hie] at he
          exact hbad he
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv.1, by omega⟩
    · intro j hj k hk he
      have hjv := (hpos j hj).2
      have hkv := (hpos k hk).2
      rw [he] at hjv
      nlinarith
  let U := (Finset.range n).filter (fun i => s.a i < 2*p ∧ 2*p ≤ s.a (i+1))
  let P := U.filter (fun i => (s.a i).Prime)
  let C := U.filter (fun i => ¬ (s.a i).Prime)
  let R := (Finset.Ioc (2*p/3) (p-1)).filter Nat.Prime
  have hCle : C.card ≤ Nat.primeCounting (Nat.sqrt (2*p)) := by
    apply s.composite_upcrossings_bound
    · intro i hi
      have hui := (Finset.mem_filter.mp hi).1
      have hcross := (Finset.mem_filter.mp hui).2
      have hi0 : i ≠ 0 := by
        intro he
        rw [he, s.seed_one] at hcross
        omega
      have hne1 : s.a i ≠ 1 := by
        intro he
        exact hi0 (s.injective (he.trans s.seed_zero.symm))
      have hpos := s.positive i
      exact ⟨by omega, (Finset.mem_filter.mp hi).2⟩
    · intro i hi
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have hPle : P.card ≤ R.card := by
    apply Finset.card_le_card_of_injOn s.a
    · intro i hi
      have hui := (Finset.mem_filter.mp hi).1
      have hil := Finset.mem_range.mp (Finset.mem_filter.mp hui).1
      have hprime := (Finset.mem_filter.mp hi).2
      have hcross := (Finset.mem_filter.mp hui).2
      have hrange := prime_upcrossing_before_introduction s h hp2 ih hil hprime hcross
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hrange.1, by omega⟩, hprime⟩
    · intro i _ j _ he
      exact s.injective he
  have hpartition : P.card + C.card = U.card := Finset.card_filter_add_card_filter_not _
  have hU : U.card = upCount s.a (2*p) n := (upCount_eq_card s.a (2*p) n).symm
  have hD : D.card = downCount s.a (2*p) n := (downCount_eq_card s.a (2*p) n).symm
  have hbal := crossing_balance s.a (2*p) n
  have hz : above s.a (2*p) 0 = 0 := by simp [above, s.seed_zero]; omega
  have hnabove : above s.a (2*p) n = 1 := by simp [above, Nat.le_of_lt hbig]
  rw [hz, hnabove] at hbal
  have hJ : J.card = (p-1)/2 - p/3 := by simp [J]
  have hR : R.card = Nat.primeCounting (p-1) - Nat.primeCounting (2*p/3) :=
    primeStructure_prime_Ioc_card _ _ (by omega)
  omega

end EKG
