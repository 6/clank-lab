import EKG.PrimeStructureGlobal
import EKG.EarlyEvens
import EKG.Targets

namespace EKG

/-- The actual finite base, not a hypothesis passed to the bootstrap. -/
theorem earlyEvenBase_verified : EarlyEvenBase := FiniteBase.earlyEvenBase

/-- Lemma EE and the sieve recurrence for the actual canonical EKG sequence.
The prime introduction theorem is proved, rather than passed as a parameter. -/
theorem earlyEvenRecurrence_verified : EarlyEvenRecurrence := by
  intro t ht
  exact early_even_recurrence_of_prime_pattern canonical
    (primeIntroductionPattern canonical) ht

/-- Theorem 1(a): unconditional early-even bound for actual EKG.
This is a finite combinatorial theorem, not the entire asymptotic result. -/
theorem earlyEvenTarget_verified : EarlyEvenTarget :=
  earlyEvenTarget_of_base_and_recurrence earlyEvenBase_verified earlyEvenRecurrence_verified

theorem earlyEvenBase_any (s : GreedySeq) :
    ∀ t, t ≤ 9 → earlyEvenCount s t ≤ 1 := by
  intro t ht
  rw [FiniteBase.earlyEvenCount_eq s (by omega : t < 13)]
  exact FiniteBase.checked_early_base ⟨t, by omega⟩

theorem early_even_bound (s : GreedySeq) (t : ℕ) :
    earlyEvenCount s t ≤
      12 * Nat.primeCounting (Nat.sqrt (frontier s t)) + 720 := by
  apply bootstrap_from_counting_recurrence (earlyEvenCount s)
    (fun u => Nat.primeCounting (Nat.sqrt (frontier s u)))
    (frontier_prime_count_monotone s) (earlyEvenBase_any s)
  intro u hu
  exact early_even_recurrence_of_prime_pattern s (primeIntroductionPattern s) hu

end EKG
