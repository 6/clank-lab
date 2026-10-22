import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Lattice.Fold
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace EKG

/-- Kernel-reduced finite arithmetic; no native_decide is used here. -/
theorem totient_210 : Nat.totient 210 = 48 := by decide

theorem sieve_210_coprime_bound (start len : ℕ) :
    ((Finset.Ico start (start + len)).filter (fun x => Nat.Coprime 210 x)).card
      ≤ 48 * (len / 210 + 1) := by
  simpa only [totient_210] using
    (Nat.Ico_filter_coprime_le (a := 210) start len (by decide))

theorem small_prime_divisors_210 : ∀ p : Fin 211,
    p.val.Prime → p.val ∣ 210 → p.val ∈ ({2, 3, 5, 7} : Finset ℕ) := by
  decide

/-- The four excluded primes are explicitly bounded; all other primes are
counted by the proved periodic coprimality estimate. -/
theorem prime_interval_sieve (start len : ℕ) :
    ((Finset.Ico start (start + len)).filter Nat.Prime).card
      ≤ 48 * (len / 210 + 1) + 4 := by
  classical
  let C := (Finset.Ico start (start + len)).filter (fun x => Nat.Coprime 210 x)
  let D : Finset ℕ := {2, 3, 5, 7}
  have hsub : (Finset.Ico start (start + len)).filter Nat.Prime ⊆ C ∪ D := by
    intro p hp
    obtain ⟨hi, hprime⟩ := Finset.mem_filter.mp hp
    by_cases hcop : Nat.Coprime 210 p
    · exact Finset.mem_union_left D (Finset.mem_filter.mpr ⟨hi, hcop⟩)
    · have hdiv : p ∣ 210 := hprime.dvd_iff_not_coprime.mpr (by
        intro h; exact hcop h.symm)
      have hle : p ≤ 210 := Nat.le_of_dvd (by decide) hdiv
      exact Finset.mem_union_right C (small_prime_divisors_210 ⟨p, by omega⟩ hprime hdiv)
  have hC : C.card ≤ 48 * (len / 210 + 1) := sieve_210_coprime_bound start len
  have hD : D.card = 4 := by decide
  calc
    _ ≤ (C ∪ D).card := Finset.card_le_card hsub
    _ ≤ C.card + D.card := Finset.card_union_le C D
    _ ≤ 48 * (len / 210 + 1) + 4 := by omega

def priorPeak (f : ℕ → ℕ) (t : ℕ) : ℕ := (Finset.range t).sup f

/-- Arithmetic closing of the induction in the manuscript. -/
theorem bootstrap_step (early primes peak : ℕ)
    (hpeak : peak ≤ 12 * primes + 720)
    (hcount : early ≤ primes + 6 + 48 * ((4 * peak + 3) / 210 + 1)) :
    early ≤ 12 * primes + 720 := by
  omega

/-- CONDITIONAL theorem. The EKG crossing-and-sieve recurrence below must
still be proved for the real early-even count; this theorem does not assert it. -/
theorem bootstrap_from_counting_recurrence (early primes : ℕ → ℕ)
    (hmono : Monotone primes)
    (hbase : ∀ t, t ≤ 9 → early t ≤ 1)
    (hrec : ∀ t, 10 ≤ t →
      early t ≤ primes t + 6 + 48 * ((4 * priorPeak early t + 3) / 210 + 1)) :
    ∀ t, early t ≤ 12 * primes t + 720 := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t ≤ 9
    · have := hbase t ht
      omega
    · have hpeak : priorPeak early t ≤ 12 * primes t + 720 := by
        apply Finset.sup_le
        intro j hj
        have hjt := Finset.mem_range.mp hj
        have hprev := ih j hjt
        have hprimes := hmono (Nat.le_of_lt hjt)
        omega
      exact bootstrap_step (early t) (primes t) (priorPeak early t) hpeak
        (hrec t (by omega))

end EKG
