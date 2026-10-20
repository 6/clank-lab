import Solution
import SolutionB
import SolutionCounting
import SolutionPNT

open EKG EKG.CanonicalCounting

-- Closed compatibility witness: each field is an actual proved endpoint.
theorem ekg_pnt_compatibility :
    (∀ delta : ℝ, 0 < delta → ∃ u0 : ℕ, ∀ u : ℕ, u0 ≤ u →
       max ((EKG.nonTickTop EKG.canonical u : ℝ) -
         (EKG.frontier EKG.canonical u : ℝ)) 0 ≤
         delta * (EKG.frontier EKG.canonical u : ℝ) /
           Real.log (EKG.frontier EKG.canonical u)) ∧
    (∀ delta : ℝ, 0 < delta → ∃ u0 : ℕ, ∀ u : ℕ, u0 ≤ u →
       ∀ h : ℕ, 2 ≤ h → ¬ h.Prime → h < EKG.frontier EKG.canonical u →
         ¬ EKG.UsedBefore EKG.canonical.a (u + 1) h →
         (EKG.frontier EKG.canonical u : ℝ) - (h : ℝ) <
           delta * (EKG.frontier EKG.canonical u : ℝ) /
             Real.log (EKG.frontier EKG.canonical u)) ∧
    (∀ u : ℕ, 8 ≤ u →
       (Clock.missingPrimes canonical u).card = (P1 u).card + theta1 u ∧
       (Clock.tickAbove canonical u spanTickValue).card + theta2 u = (P2 u).card ∧
       (P1 u).card + Nat.primeCounting (EKG.CanonicalCounting.e u / 2) =
         Nat.primeCounting (EKG.CanonicalCounting.e u) + halfPrimeIndicator u ∧
       (P2 u).card + Nat.primeCounting (EKG.CanonicalCounting.e u / 3) + halfPrimeIndicator u =
         Nat.primeCounting (EKG.CanonicalCounting.e u / 2) ∧
       theta u ≤ 2 ∧ 1 ≤ correction u ∧ correction u ≤ 5 ∧
       (EKG.CanonicalCounting.e u : ℤ) - ((u + 1 : ℕ) : ℤ) =
         (Nat.primeCounting (EKG.CanonicalCounting.e u) : ℤ) -
           2 * (Nat.primeCounting (EKG.CanonicalCounting.e u / 2) : ℤ) +
           (Nat.primeCounting (EKG.CanonicalCounting.e u / 3) : ℤ) +
           (H u : ℤ) - (K u : ℤ) - (O u : ℤ) + (correction u : ℤ)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
       |(Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x| ≤
         ε * (x / Real.log x)) := by
  exact ⟨ekg_part_a, ekg_part_b, ekg_exact_counting, ekg_weak_pnt⟩

#print axioms ekg_pnt_compatibility
