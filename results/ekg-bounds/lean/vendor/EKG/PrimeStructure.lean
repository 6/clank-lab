import EKG.Canonical
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring

/-! Prime introductions for the actual EKG greedy rule (2 is eligible).
The exceptional prime 2 is introduced at the seed a(1)=2. For every other
prime, the first multiple is q*p for an already introduced prime q, and
the following term is p. No assumption about the global 2p pattern is
used in these results. All indices are zero based. -/
namespace EKG

def NewPrimeAt (s : GreedySeq) (n p : ℕ) : Prop :=
  p.Prime ∧ p ∣ s.a n ∧ ∀ i < n, ¬ p ∣ s.a i

theorem newPrime_two_seed (s : GreedySeq) : NewPrimeAt s 1 2 := by
  refine ⟨Nat.prime_two, by rw [s.seed_one], ?_⟩
  intro i hi
  have : i = 0 := by omega
  subst i
  rw [s.seed_zero]
  omega

theorem newPrime_index (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) : 2 ≤ n := by
  have hp := h.1.two_le
  by_contra hn
  have hc : n = 0 ∨ n = 1 := by omega
  rcases hc with hc | hc <;> subst n
  · have hd := h.2.1
    rw [s.seed_zero] at hd
    have := Nat.le_of_dvd (by omega : 0 < 1) hd
    omega
  · have hd := h.2.1
    rw [s.seed_one] at hd
    have := Nat.le_of_dvd (by omega : 0 < 2) hd
    omega

theorem newPrime_unused_multiple (s : GreedySeq) {n p k : ℕ}
    (h : NewPrimeAt s n p) : ¬ UsedBefore s.a n (k*p) := by
  rintro ⟨i, hi, he⟩
  apply h.2.2 i hi
  rw [he]
  exact Nat.dvd_mul_left p k

theorem term_unused (s : GreedySeq) (n : ℕ) : ¬ UsedBefore s.a n (s.a n) := by
  rintro ⟨i, hi, he⟩
  have := s.injective he
  omega

theorem firstMultiple_eq_mul (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) :
    ∃ q : ℕ, q.Prime ∧ q ∣ s.a (n-1) ∧ s.a n = q*p ∧ q ≠ p := by
  have hn := newPrime_index s h hp2
  obtain ⟨q, hq, hqb, hqm⟩ := s.eligible n hn
  have hqp : q ≠ p := by
    intro he
    subst q
    exact h.2.2 (n-1) (by omega) hqb
  have hprod : q*p ∣ s.a n := by
    obtain ⟨k, hk⟩ := h.2.1
    have hqk : q ∣ k := by
      rcases hq.dvd_mul.mp (hk ▸ hqm) with hqdiv | hqdiv
      · rcases (Nat.dvd_prime h.1).mp hqdiv with he | he
        · exact (hq.ne_one he).elim
        · exact (hqp he).elim
      · exact hqdiv
    obtain ⟨l, hl⟩ := hqk
    refine ⟨l, ?_⟩
    rw [hk, hl]
    ring
  have hlo : q*p ≤ s.a n := Nat.le_of_dvd (s.positive n) hprod
  have hhi : s.a n ≤ q*p := s.minimal n hn (q*p)
    (Nat.mul_pos hq.pos h.1.pos) (newPrime_unused_multiple s h)
    ⟨q, hq, hqb, Nat.dvd_mul_right q p⟩
  exact ⟨q, hq, hqb, le_antisymm hhi hlo, hqp⟩

theorem firstMultiple_composite (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) :
    1 < s.a n ∧ ¬ (s.a n).Prime := by
  obtain ⟨q, hq, _, heq, _⟩ := firstMultiple_eq_mul s h hp2
  have hq2 := hq.two_le
  have hp := h.1.two_le
  refine ⟨by rw [heq]; nlinarith, ?_⟩
  apply Nat.not_prime_of_dvd_of_lt h.2.1 hp
  rw [heq]
  nlinarith

theorem firstMultiple_next_prime (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) : s.a (n+1) = p := by
  have hn := newPrime_index s h hp2
  obtain ⟨q, hq, hqb, heq, hqp⟩ := firstMultiple_eq_mul s h hp2
  have hunused : ¬ UsedBefore s.a (n+1) p := by
    rintro ⟨i, hi, he⟩
    by_cases hin : i < n
    · apply h.2.2 i hin
      rw [he]
    · have hi' : i = n := by omega
      subst i
      rw [he] at heq
      have htwo := hq.two_le
      have hp := h.1.pos
      nlinarith
  have hprev : n+1-1 = n := by omega
  have hle : s.a (n+1) ≤ p := by
    apply s.minimal (n+1) (by omega) p h.1.pos hunused
    rw [hprev]
    exact ⟨p, h.1, h.2.1, dvd_refl p⟩
  obtain ⟨r, hr, hrc, hrnext⟩ := s.eligible (n+1) (by omega)
  rw [hprev, heq] at hrc
  rcases hr.dvd_mul.mp hrc with hrq | hrp
  · rcases (Nat.dvd_prime hq).mp hrq with he | he
    · exact (hr.ne_one he).elim
    · subst r
      have hfree : ¬ UsedBefore s.a n (s.a (n+1)) := by
        rintro ⟨i, hi, hei⟩
        have := s.injective hei
        omega
      have hbad := s.minimal n hn (s.a (n+1)) (s.positive (n+1)) hfree
        ⟨q, hq, hqb, hrnext⟩
      rw [heq] at hbad
      have htwo := hq.two_le
      have hp := h.1.pos
      nlinarith
  · rcases (Nat.dvd_prime h.1).mp hrp with he | he
    · exact (hr.ne_one he).elim
    · subst r
      exact le_antisymm hle (Nat.le_of_dvd (s.positive (n+1)) hrnext)

theorem smaller_divisor_seen (s : GreedySeq) {n p r : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) (hr : 0 < r) (hrp : r < p) :
    ∃ i < n, r ∣ s.a i := by
  have hn := newPrime_index s h hp2
  obtain ⟨q, hq, hqb, heq, _⟩ := firstMultiple_eq_mul s h hp2
  by_contra hnone
  have hfree : ¬ UsedBefore s.a n (q*r) := by
    rintro ⟨i, hi, hei⟩
    apply hnone
    refine ⟨i, hi, ?_⟩
    rw [hei]
    exact Nat.dvd_mul_left r q
  have hbad := s.minimal n hn (q*r) (Nat.mul_pos hq.pos hr) hfree
    ⟨q, hq, hqb, Nat.dvd_mul_right q r⟩
  rw [heq] at hbad
  have hqpos := hq.pos
  nlinarith

theorem prior_prime_lt (s : GreedySeq) {n p i r : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) (hi : i < n)
    (hr : r.Prime) (hrdiv : r ∣ s.a i) : r < p := by
  by_cases hr2 : r = 2
  · have hp := h.1.two_le
    omega
  by_contra hnot
  have hne : r ≠ p := by
    intro he
    subst r
    exact h.2.2 i hi hrdiv
  have hpr : p < r := by omega
  have hex : ∃ j, r ∣ s.a j := ⟨i, hrdiv⟩
  let j := Nat.find hex
  have hji : j ≤ i := Nat.find_min' hex hrdiv
  have hnewr : NewPrimeAt s j r := by
    refine ⟨hr, Nat.find_spec hex, ?_⟩
    intro k hk
    exact Nat.find_min hex hk
  obtain ⟨k, hkj, hkdiv⟩ := smaller_divisor_seen s hnewr hr2 h.1.pos hpr
  exact h.2.2 k (by omega) hkdiv

theorem firstMultiple_factor_lt (s : GreedySeq) {n p : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ q ∣ s.a (n-1) ∧ s.a n = q*p := by
  obtain ⟨q, hq, hqb, heq, _⟩ := firstMultiple_eq_mul s h hp2
  have hn := newPrime_index s h hp2
  exact ⟨q, hq, prior_prime_lt s h hp2 (by omega) hq hqb, hqb, heq⟩

theorem lower_multiple_used (s : GreedySeq) {n p q k : ℕ}
    (h : NewPrimeAt s n p) (hp2 : p ≠ 2) (hq : q.Prime)
    (hqb : q ∣ s.a (n-1)) (heq : s.a n = q*p)
    (hk : 0 < k) (hkp : k < p) : UsedBefore s.a n (q*k) := by
  by_contra hfree
  have hbad := s.minimal n (newPrime_index s h hp2) (q*k)
    (Nat.mul_pos hq.pos hk) hfree ⟨q, hq, hqb, Nat.dvd_mul_right q k⟩
  rw [heq] at hbad
  have hqpos := hq.pos
  nlinarith

theorem primeFactor_lt_absent (s : GreedySeq) {p i r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (habs : ∀ n, ¬ p ∣ s.a n)
    (hr : r.Prime) (hrdiv : r ∣ s.a i) : r < p := by
  by_cases hr2 : r = 2
  · have hp' := hp.two_le
    omega
  by_contra hnot
  have hne : r ≠ p := by
    intro he
    subst r
    exact habs i hrdiv
  have hpr : p < r := by omega
  have hex : ∃ j, r ∣ s.a j := ⟨i, hrdiv⟩
  have hnew : NewPrimeAt s (Nat.find hex) r := by
    refine ⟨hr, Nat.find_spec hex, ?_⟩
    intro k hk
    exact Nat.find_min hex hk
  obtain ⟨k, _, hkdiv⟩ := smaller_divisor_seen s hnew hr2 hp.pos hpr
  exact habs k hkdiv

theorem bounded_if_prime_absent (s : GreedySeq) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (habs : ∀ n, ¬ p ∣ s.a n) :
    ∀ n, s.a n < p*p+1 := by
  intro n
  by_cases hn : 2 ≤ n
  · obtain ⟨r, hr, hrprev, _⟩ := s.eligible n hn
    have hrp := primeFactor_lt_absent s hp hp2 habs hr hrprev
    have hfree : ¬ UsedBefore s.a n (r*p) := by
      rintro ⟨i, _, hei⟩
      apply habs i
      rw [hei]
      exact Nat.dvd_mul_left p r
    have hle := s.minimal n hn (r*p) (Nat.mul_pos hr.pos hp.pos) hfree
      ⟨r, hr, hrprev, Nat.dvd_mul_right r p⟩
    nlinarith
  · have hc : n = 0 ∨ n = 1 := by omega
    have hp' := hp.two_le
    rcases hc with hc | hc <;> subst n
    · rw [s.seed_zero]; nlinarith
    · rw [s.seed_one]; nlinarith

theorem every_prime_introduced (s : GreedySeq) {p : ℕ}
    (hp : p.Prime) : ∃ n, NewPrimeAt s n p := by
  by_cases hp2 : p = 2
  · subst p
    exact ⟨1, newPrime_two_seed s⟩
  have hex : ∃ n, p ∣ s.a n := by
    by_contra hnone
    have habs : ∀ n, ¬ p ∣ s.a n := by
      intro n hn
      exact hnone ⟨n, hn⟩
    have hbound := bounded_if_prime_absent s hp hp2 habs
    let f : ℕ → Fin (p*p+1) := fun n => ⟨s.a n, hbound n⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply s.injective
      exact congrArg Fin.val hij
    haveI : Finite ℕ := Finite.of_injective f hf
    exact not_finite ℕ
  refine ⟨Nat.find hex, hp, Nat.find_spec hex, ?_⟩
  intro i hi
  exact Nat.find_min hex hi

theorem every_prime_occurs (s : GreedySeq) {p : ℕ}
    (hp : p.Prime) : ∃ n, s.a n = p := by
  by_cases hp2 : p = 2
  · exact ⟨1, s.seed_one.trans hp2.symm⟩
  obtain ⟨n, hn⟩ := every_prime_introduced s hp
  exact ⟨n+1, firstMultiple_next_prime s hn hp2⟩

/-- Backlink from an arbitrary odd-prime occurrence to its first introduction.
The lower bound is in zero-based indexing. -/
theorem primeOccurrenceIntro (s : GreedySeq) {i p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (heq : s.a i = p) :
    3 ≤ i ∧ NewPrimeAt s (i-1) p := by
  obtain ⟨n, hn⟩ := every_prime_introduced s hp
  have hnext := firstMultiple_next_prime s hn hp2
  have hindex : n+1 = i := s.injective (hnext.trans heq.symm)
  have hn2 := newPrime_index s hn hp2
  refine ⟨by omega, ?_⟩
  have he : i-1 = n := by omega
  simpa [he] using hn

theorem newPrime_order (s : GreedySeq) {n m p r : ℕ}
    (hp : NewPrimeAt s n p) (hr : NewPrimeAt s m r) (hpr : p < r) : n < m := by
  have hr2 : r ≠ 2 := by have := hp.1.two_le; omega
  obtain ⟨i, him, hdiv⟩ := smaller_divisor_seen s hr hr2 hp.1.pos hpr
  by_contra hnot
  exact hp.2.2 i (by omega) hdiv

end EKG
