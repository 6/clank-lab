import EKG.CountingDefinitions
import EKG.PrimeStructureGlobal

/-!
Canonical odd-prime introductions and literal prefix occurrences.
The first-divisibility predicate is the unchanged upstream `NewPrimeAt`.
Only finite structural facts and injectivity are used here.
-/

namespace EKG.CanonicalCounting

/-- A prime has only one first-divisibility index. -/
theorem introduction_unique {n m p : ℕ}
    (hn : NewPrimeAt canonical n p) (hm : NewPrimeAt canonical m p) : n = m := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hnm | hmn
  · exact hm.2.2 n hnm hn.2.1
  · exact hn.2.2 m hmn hm.2.1

/-- Distinct odd primes cannot be introduced at the same canonical index. -/
theorem introduction_prime_unique {n p q : ℕ}
    (hp : NewPrimeAt canonical n p) (hp2 : p ≠ 2)
    (hq : NewPrimeAt canonical n q) (hq2 : q ≠ 2) : p = q := by
  have hpp := firstMultiple_eq_twice canonical hp hp2
  have hqq := firstMultiple_eq_twice canonical hq hq2
  omega

/-- The actual canonical block at an odd prime's unique introduction. -/
theorem introduction_block {n p : ℕ}
    (hnew : NewPrimeAt canonical n p) (hp2 : p ≠ 2) :
    canonical.a n = 2 * p ∧ canonical.a (n + 1) = p ∧
      canonical.a (n + 2) = 3 * p :=
  firstMultiple_triple canonical hnew hp2

/-- Every odd prime has a unique introduction, with its complete actual
`2p,p,3p` block. The witness is an index, not a freely chosen function.
-/
theorem odd_prime_introduction {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃! n : ℕ, NewPrimeAt canonical n p ∧ canonical.a n = 2 * p ∧
      canonical.a (n + 1) = p ∧ canonical.a (n + 2) = 3 * p := by
  obtain ⟨n, hn, hfirst, hprime, htick⟩ := odd_prime_triple_exists canonical hp hp2
  refine ⟨n, ⟨hn, hfirst, hprime, htick⟩, ?_⟩
  intro m hm
  exact introduction_unique hm.1 hn

/-- Canonical injectivity translates an actual occurrence into the exact
inclusive-prefix cutoff; the observed entries are `0,...,u`.
-/
theorem used_iff_occurrence_le {u k m : ℕ} (hocc : canonical.a k = m) :
    UsedBefore canonical.a (u + 1) m ↔ k ≤ u := by
  constructor
  · rintro ⟨i, hi, hval⟩
    have hik : i = k := canonical.injective (hval.trans hocc.symm)
    omega
  · intro hk
    exact ⟨k, by omega, hocc⟩

theorem twice_used_iff {u n p : ℕ}
    (hnew : NewPrimeAt canonical n p) (hp2 : p ≠ 2) :
    UsedBefore canonical.a (u + 1) (2 * p) ↔ n ≤ u :=
  used_iff_occurrence_le (introduction_block hnew hp2).1

theorem prime_used_iff {u n p : ℕ}
    (hnew : NewPrimeAt canonical n p) (hp2 : p ≠ 2) :
    UsedBefore canonical.a (u + 1) p ↔ n + 1 ≤ u :=
  used_iff_occurrence_le (introduction_block hnew hp2).2.1

theorem tick_used_iff {u n p : ℕ}
    (hnew : NewPrimeAt canonical n p) (hp2 : p ≠ 2) :
    UsedBefore canonical.a (u + 1) (3 * p) ↔ n + 2 ≤ u :=
  used_iff_occurrence_le (introduction_block hnew hp2).2.2

/-- An observed odd-prime introduction lies strictly below the present
least unused even; equality is excluded because `2p` is already used.
-/
theorem introduction_before_frontier {u n p : ℕ}
    (hnew : NewPrimeAt canonical n p) (hp2 : p ≠ 2) (hnu : n ≤ u) :
    2 * p < frontier canonical u :=
  prime_introduction_before_frontier canonical hnew hp2 hnu

/-- Conversely, an even `2p` below the frontier has already occurred, so
the unique introduction index is already in the observed prefix.
-/
theorem introduction_le_iff_twice_lt_frontier {u n p : ℕ}
    (hnew : NewPrimeAt canonical n p) (hp2 : p ≠ 2) :
    n ≤ u ↔ 2 * p < frontier canonical u := by
  constructor
  · exact introduction_before_frontier hnew hp2
  · intro hsmall
    apply (twice_used_iff hnew hp2).mp
    exact smaller_even_used canonical
      (Nat.mul_pos (by decide : 0 < 2) hnew.1.pos)
      (Nat.dvd_mul_right 2 p) hsmall

/-- Odd-prime introductions are separated by the entire intervening block. -/
theorem introduction_separated {n m p q : ℕ}
    (hp : NewPrimeAt canonical n p) (hp2 : p ≠ 2)
    (hq : NewPrimeAt canonical m q) (hq2 : q ≠ 2) (hnm : n < m) :
    n + 4 ≤ m :=
  prime_introductions_separated canonical hp hp2 hq hq2 hnm

end EKG.CanonicalCounting
