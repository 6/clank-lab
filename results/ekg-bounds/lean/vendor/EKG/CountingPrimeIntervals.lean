import EKG.CountingDefinitions
import EKG.EarlyEvens

/-! Exact inclusive prime-count formulas for the two frozen prime intervals.
Only the half endpoint contributes an indicator. The strict third endpoint
is accounted for by the inclusive count `primeCounting (e / 3)` itself.
-/

namespace EKG.CanonicalCounting

open Finset

theorem counting_frontier_even (u : ℕ) : 2 ∣ e u :=
  (frontier_spec canonical u).2.1

theorem counting_frontier_half_twice (u : ℕ) : 2 * (e u / 2) = e u :=
  Nat.mul_div_cancel' (counting_frontier_even u)

theorem counting_frontier_ge_fourteen {u : ℕ} (hu : 8 ≤ u) : 14 ≤ e u :=
  frontier_ge_fourteen canonical hu

theorem counting_frontier_not_prime {u : ℕ} (hu : 8 ≤ u) : ¬ (e u).Prime := by
  intro hp
  have heq : 2 = e u :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (counting_frontier_even u)
  have hge := counting_frontier_ge_fourteen hu
  omega

/-- Strict counting and the one possible endpoint prime give inclusive pi. -/
theorem primesBelow_card_add_indicator (n : ℕ) :
    n.primesBelow.card + (if n.Prime then 1 else 0) = Nat.primeCounting n := by
  classical
  rw [Nat.primesBelow_card_eq_primeCounting']
  exact (Nat.count_succ Nat.Prime n).symm

theorem primesBelow_succ_card (n : ℕ) :
    (n + 1).primesBelow.card = Nat.primeCounting n :=
  Nat.primesBelow_card_eq_primeCounting' (n + 1)

/-- The frozen half-open interval `[e/2,e)` includes a prime exactly at
the half endpoint, while the inclusive pi at `e` adds no prime at `e`. -/
theorem P1_card_primeCounting {u : ℕ} (hu : 8 ≤ u) :
    (P1 u).card + Nat.primeCounting (e u / 2) =
      Nat.primeCounting (e u) + halfPrimeIndicator u := by
  classical
  have he := counting_frontier_ge_fourteen hu
  have htwice := counting_frontier_half_twice u
  have hcomplement :
      ((e u).primesBelow.filter (fun p => ¬ e u ≤ 2 * p)) =
        (e u / 2).primesBelow := by
    ext p
    simp only [mem_filter, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hpe, hp⟩, hcut⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hph, hp⟩
      exact ⟨⟨by omega, hp⟩, by omega⟩
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (e u).primesBelow) (fun p => e u ≤ 2 * p)
  rw [hcomplement] at hpartition
  change (P1 u).card + (e u / 2).primesBelow.card = (e u).primesBelow.card
    at hpartition
  have htotal : (e u).primesBelow.card = Nat.primeCounting (e u) := by
    have h := primesBelow_card_add_indicator (e u)
    simpa only [if_neg (counting_frontier_not_prime hu), Nat.add_zero] using h
  have hhalf := primesBelow_card_add_indicator (e u / 2)
  change (e u / 2).primesBelow.card + halfPrimeIndicator u =
    Nat.primeCounting (e u / 2) at hhalf
  omega

/-- Both multiplicative inequalities defining P2 are strict. The lower
complement is exactly all primes at most `floor(e/3)`, including a prime
there when `3*p=e`, so no floor-third indicator is introduced. -/
theorem P2_card_primeCounting {u : ℕ} (hu : 8 ≤ u) :
    (P2 u).card + Nat.primeCounting (e u / 3) + halfPrimeIndicator u =
      Nat.primeCounting (e u / 2) := by
  classical
  have he := counting_frontier_ge_fourteen hu
  have htwice := counting_frontier_half_twice u
  have hinterval :
      ((e u / 2).primesBelow.filter (fun p => e u < 3 * p)) = P2 u := by
    ext p
    simp only [P2, mem_filter, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hph, hp⟩, hthird⟩
      exact ⟨⟨by omega, hp⟩, hthird, by omega⟩
    · rintro ⟨⟨hpe, hp⟩, hthird, hhalf⟩
      exact ⟨⟨by omega, hp⟩, hthird⟩
  have hcomplement :
      ((e u / 2).primesBelow.filter (fun p => ¬ e u < 3 * p)) =
        (e u / 3 + 1).primesBelow := by
    ext p
    simp only [mem_filter, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hph, hp⟩, hthird⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpthird, hp⟩
      exact ⟨⟨by omega, hp⟩, by omega⟩
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (e u / 2).primesBelow) (fun p => e u < 3 * p)
  rw [hinterval, hcomplement, primesBelow_succ_card] at hpartition
  have hhalf := primesBelow_card_add_indicator (e u / 2)
  change (e u / 2).primesBelow.card + halfPrimeIndicator u =
    Nat.primeCounting (e u / 2) at hhalf
  omega

end EKG.CanonicalCounting
