import EKG.Frontier
import EKG.Bootstrap
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Sqrt

namespace EKG

def smoothValue (m : ℕ) : ℕ :=
  if m.Prime then 2*m else
  if (m/3).Prime ∧ m = 3*(m/3) then 2*(m/3) else m

/-- The main proposition, proved by `EKG.mainRate` in `EKG.MainRate`.
Index n in actualA corresponds to manuscript index n+1. -/
def MainRateTarget : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |(smoothValue (actualA n) : ℝ) - (n+1 : ℕ)| ≤
      C * ((n+1 : ℕ) : ℝ) / Real.log ((n+1 : ℕ) : ℝ)

/-- The early-even proposition, proved in `EKG.VerifiedCounts`. -/
def EarlyEvenTarget : Prop := ∀ t,
  earlyEvenCount canonical t ≤ 12 * Nat.primeCounting (Nat.sqrt (frontier canonical t)) + 720

def EarlyEvenBase : Prop := ∀ t, t ≤ 9 → earlyEvenCount canonical t ≤ 1

/-- The self-pairing/crossing recurrence, established in `EKG.VerifiedCounts`. -/
def EarlyEvenRecurrence : Prop := ∀ t, 10 ≤ t →
  earlyEvenCount canonical t ≤ Nat.primeCounting (Nat.sqrt (frontier canonical t)) +
    6 + 48 * ((4 * priorPeak (earlyEvenCount canonical) t + 3) / 210 + 1)

/-- Conditional bootstrap interface. Both explicit hypotheses are discharged
for the actual sequence by the theorems in `EKG.VerifiedCounts`. -/
theorem earlyEvenTarget_of_base_and_recurrence
    (hbase : EarlyEvenBase) (hrec : EarlyEvenRecurrence) : EarlyEvenTarget :=
  bootstrap_from_counting_recurrence (earlyEvenCount canonical)
    (fun t => Nat.primeCounting (Nat.sqrt (frontier canonical t)))
    (frontier_prime_count_monotone canonical) hbase hrec

end EKG
