import EKG.PrimeStructure
import EKG.Frontier

/-! Least-multiple and local prime-pattern consequences. The hypothesis
`a n = 2*p` below is stated explicitly. The unconditional global theorem
that every odd prime is introduced at 2p is proved in PrimeStructureGlobal. -/
namespace EKG

theorem unused_prime_multiple_exists (s : GreedySeq) (t p : ℕ) (hp : 0 < p) :
    ∃ m, 0 < m ∧ p ∣ m ∧ ¬ UsedBefore s.a (t+1) m := by
  let M := (Finset.range (t+1)).sup s.a
  refine ⟨p*(M+1), Nat.mul_pos hp (by omega), Nat.dvd_mul_right p (M+1), ?_⟩
  rintro ⟨i, hi, he⟩
  have hb : s.a i ≤ M := Finset.le_sup (Finset.mem_range.mpr hi)
  nlinarith

noncomputable def leastUnusedMultiple (s : GreedySeq) (t p : ℕ) (hp : 0 < p) : ℕ := by
  classical
  exact Nat.find (unused_prime_multiple_exists s t p hp)

theorem leastUnusedMultiple_spec (s : GreedySeq) (t p : ℕ) (hp : 0 < p) :
    0 < leastUnusedMultiple s t p hp ∧ p ∣ leastUnusedMultiple s t p hp ∧
      ¬ UsedBefore s.a (t+1) (leastUnusedMultiple s t p hp) := by
  classical
  exact Nat.find_spec (unused_prime_multiple_exists s t p hp)

theorem leastUnusedMultiple_le (s : GreedySeq) {t p m : ℕ} (hp : 0 < p)
    (hm : 0 < m) (hdiv : p ∣ m) (hfree : ¬ UsedBefore s.a (t+1) m) :
    leastUnusedMultiple s t p hp ≤ m := by
  classical
  exact Nat.find_min' (unused_prime_multiple_exists s t p hp) ⟨hm, hdiv, hfree⟩

theorem next_le_leastUnusedMultiple (s : GreedySeq) {t p : ℕ}
    (ht : 1 ≤ t) (hp : p.Prime) (hdiv : p ∣ s.a t) :
    s.a (t+1) ≤ leastUnusedMultiple s t p hp.pos := by
  have hb := leastUnusedMultiple_spec s t p hp.pos
  apply s.minimal (t+1) (by omega) _ hb.1 hb.2.2
  have he : t+1-1 = t := by omega
  rw [he]
  exact ⟨p, hp, hdiv, hb.2.1⟩

theorem after_prime_eq_leastUnusedMultiple (s : GreedySeq) {t p : ℕ}
    (ht : 1 ≤ t) (hp : p.Prime) (heq : s.a t = p) :
    s.a (t+1) = leastUnusedMultiple s t p hp.pos := by
  apply le_antisymm (next_le_leastUnusedMultiple s ht hp (heq ▸ dvd_refl p))
  apply leastUnusedMultiple_le s hp.pos (s.positive _) _ (term_unused s _)
  obtain ⟨r, hr, hrprev, hrnext⟩ := s.eligible (t+1) (by omega)
  have he : t+1-1 = t := by omega
  rw [he, heq] at hrprev
  rcases (Nat.dvd_prime hp).mp hrprev with he | he
  · exact (hr.ne_one he).elim
  · simpa [he] using hrnext

theorem after_prime_eq_multiple (s : GreedySeq) {t p k : ℕ}
    (ht : 1 ≤ t) (hp : p.Prime) (heq : s.a t = p) (hk : 0 < k)
    (hfree : ¬ UsedBefore s.a (t+1) (k*p))
    (hsmall : ∀ j, 0 < j → j < k → UsedBefore s.a (t+1) (j*p)) :
    s.a (t+1) = k*p := by
  have hprev : t+1-1 = t := by omega
  have hle : s.a (t+1) ≤ k*p := by
    apply s.minimal (t+1) (by omega) _ (Nat.mul_pos hk hp.pos) hfree
    rw [hprev, heq]
    exact ⟨p, hp, dvd_refl p, Nat.dvd_mul_left p k⟩
  obtain ⟨r, hr, hrprev, hrnext⟩ := s.eligible (t+1) (by omega)
  rw [hprev, heq] at hrprev
  have hrp : r = p := by
    rcases (Nat.dvd_prime hp).mp hrprev with he | he
    · exact (hr.ne_one he).elim
    · exact he
  subst r
  obtain ⟨j, hj⟩ := hrnext
  have hpos := s.positive (t+1)
  have hp0 := hp.pos
  have hj0 : 0 < j := by
    by_contra h
    have hjz : j = 0 := by omega
    rw [hjz, Nat.mul_zero] at hj
    omega
  have hjk : k ≤ j := by
    by_contra h
    have hu := hsmall j hj0 (by omega)
    apply term_unused s (t+1)
    simpa [hj, Nat.mul_comm] using hu
  apply le_antisymm hle
  nlinarith

theorem prime_multiples_after_prime (s : GreedySeq) {n p q x : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) (heq : s.a n = q*p)
    (hx : p ∣ x) :
    UsedBefore s.a (n+2) x ↔ x = q*p ∨ x = p := by
  have hnext := firstMultiple_next_prime s h hp2
  constructor
  · rintro ⟨i, hi, hei⟩
    by_cases hin : i < n
    · exact (h.2.2 i hin (hei ▸ hx)).elim
    · have hc : i = n ∨ i = n+1 := by omega
      rcases hc with hc | hc <;> subst i
      · exact Or.inl (hei.symm.trans heq)
      · exact Or.inr (hei.symm.trans hnext)
  · rintro (hx | hx)
    · exact ⟨n, by omega, heq.trans hx.symm⟩
    · exact ⟨n+1, by omega, hnext.trans hx.symm⟩

theorem firstMultiple_next_three_of_twice (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) (heq : s.a n = 2*p) :
    s.a (n+2) = 3*p := by
  have hp0 := h.1.pos
  have hnext := firstMultiple_next_prime s h hp2
  have hfree : ¬ UsedBefore s.a (n+2) (3*p) := by
    rw [prime_multiples_after_prime s h hp2 heq (Nat.dvd_mul_left p 3)]
    omega
  have hsmall : ∀ j, 0 < j → j < 3 → UsedBefore s.a (n+2) (j*p) := by
    intro j hj hj3
    have hc : j = 1 ∨ j = 2 := by omega
    rcases hc with hc | hc <;> subst j
    · exact ⟨n+1, by omega, by simpa using hnext⟩
    · exact ⟨n, by omega, heq⟩
  have hr := after_prime_eq_multiple s (t := n+1) (by omega) h.1 hnext
    (by omega : 0 < 3) hfree hsmall
  simpa [Nat.add_assoc] using hr

theorem firstMultiple_next_twice_of_not_twice (s : GreedySeq) {n p q : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (heq : s.a n = q*p) : s.a (n+2) = 2*p := by
  have hp0 := h.1.pos
  have hnext := firstMultiple_next_prime s h hp2
  have hfree : ¬ UsedBefore s.a (n+2) (2*p) := by
    rw [prime_multiples_after_prime s h hp2 heq (Nat.dvd_mul_left p 2)]
    rintro (he | he)
    · have : q = 2 := by nlinarith
      exact hq2 this
    · omega
  have hsmall : ∀ j, 0 < j → j < 2 → UsedBefore s.a (n+2) (j*p) := by
    intro j hj hj2
    have : j = 1 := by omega
    subst j
    exact ⟨n+1, by omega, by simpa using hnext⟩
  have hr := after_prime_eq_multiple s (t := n+1) (by omega) h.1 hnext
    (by omega : 0 < 2) hfree hsmall
  simpa [Nat.add_assoc] using hr

theorem prime_multiples_after_tick (s : GreedySeq) {n p x : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) (heq : s.a n = 2*p) (hx : p ∣ x) :
    UsedBefore s.a (n+3) x ↔ x = 2*p ∨ x = p ∨ x = 3*p := by
  have htick := firstMultiple_next_three_of_twice s h hp2 heq
  constructor
  · rintro ⟨i, hi, hei⟩
    by_cases hin : i < n+2
    · have hu := (prime_multiples_after_prime s h hp2 heq hx).mp ⟨i, hin, hei⟩
      rcases hu with hu | hu
      · exact Or.inl hu
      · exact Or.inr (Or.inl hu)
    · have : i = n+2 := by omega
      subst i
      exact Or.inr (Or.inr (hei.symm.trans htick))
  · rintro (hx | hx | hx)
    · exact ⟨n, by omega, heq.trans hx.symm⟩
    · exact ⟨n+1, by omega, (firstMultiple_next_prime s h hp2).trans hx.symm⟩
    · exact ⟨n+2, by omega, htick.trans hx.symm⟩

theorem leastUnusedMultiple_after_tick (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) (heq : s.a n = 2*p) :
    leastUnusedMultiple s (n+2) p h.1.pos = 4*p := by
  have hp0 := h.1.pos
  have hfree : ¬ UsedBefore s.a (n+3) (4*p) := by
    rw [prime_multiples_after_tick s h hp2 heq (Nat.dvd_mul_left p 4)]
    omega
  have hle : leastUnusedMultiple s (n+2) p h.1.pos ≤ 4*p := by
    apply leastUnusedMultiple_le s h.1.pos (by omega) (Nat.dvd_mul_left p 4)
    simpa [Nat.add_assoc] using hfree
  have hb := leastUnusedMultiple_spec s (n+2) p h.1.pos
  obtain ⟨k, hk⟩ := hb.2.1
  have hk4 : 4 ≤ k := by
    by_contra hnot
    have hk0 : 0 < k := by
      by_contra h
      have hkz : k = 0 := by omega
      rw [hkz, Nat.mul_zero] at hk
      omega
    have hu : UsedBefore s.a (n+3) (p*k) := by
      apply (prime_multiples_after_tick s h hp2 heq (Nat.dvd_mul_right p k)).mpr
      have hc : k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hc with hc | hc | hc <;> subst k <;> simp [Nat.mul_comm]
    apply hb.2.2
    simpa [hk, Nat.add_assoc] using hu
  apply le_antisymm hle
  nlinarith

theorem firstMultiple_eq_twice_iff_even_predecessor (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) :
    s.a n = 2*p ↔ 2 ∣ s.a (n-1) := by
  have hn := newPrime_index s h hp2
  constructor
  · intro heq
    obtain ⟨q, hq, hqb, hqnext⟩ := s.eligible n hn
    rw [heq] at hqnext
    rcases hq.dvd_mul.mp hqnext with hqdiv | hqdiv
    · rcases (Nat.dvd_prime Nat.prime_two).mp hqdiv with he | he
      · exact (hq.ne_one he).elim
      · simpa [he] using hqb
    · rcases (Nat.dvd_prime h.1).mp hqdiv with he | he
      · exact (hq.ne_one he).elim
      · subst q
        exact (h.2.2 (n-1) (by omega) hqb).elim
  · intro heven
    have hle := s.minimal n hn (2*p) (by have := h.1.pos; omega)
      (newPrime_unused_multiple s h) ⟨2, Nat.prime_two, heven, Nat.dvd_mul_right 2 p⟩
    obtain ⟨q, hq, _, heq, _⟩ := firstMultiple_eq_mul s h hp2
    have hq2 := hq.two_le
    have hp0 := h.1.pos
    nlinarith

theorem firstMultiple_frontier_of_twice (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) (heq : s.a n = 2*p) :
    frontier s (n-1) = 2*p := by
  classical
  have hn := newPrime_index s h hp2
  have ht : n-1+1 = n := by omega
  have heven := (firstMultiple_eq_twice_iff_even_predecessor s h hp2).mp heq
  have hf := frontier_spec s (n-1)
  have hle : frontier s (n-1) ≤ 2*p := by
    apply Nat.find_min' (unused_even_exists s (n-1))
    refine ⟨by have := h.1.pos; omega, Nat.dvd_mul_right 2 p, ?_⟩
    rw [ht]
    exact newPrime_unused_multiple s h
  have hge : s.a n ≤ frontier s (n-1) := by
    apply s.minimal n hn _ hf.1
    · simpa [ht] using hf.2.2
    · exact ⟨2, Nat.prime_two, heven, hf.2.1⟩
  rw [heq] at hge
  exact le_antisymm hle hge

theorem firstMultiple_three_eq_six (s : GreedySeq) {n : ℕ}
    (h : NewPrimeAt s n 3) : s.a n = 6 := by
  obtain ⟨q, hq, hq3, _, heq⟩ := firstMultiple_factor_lt s h (by omega)
  have hq2 := hq.two_le
  have : q = 2 := by omega
  simpa [this] using heq

end EKG
