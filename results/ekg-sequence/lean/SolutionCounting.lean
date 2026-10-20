import EKG.CountingExact

open EKG EKG.CanonicalCounting

-- Canonical finite endpoint; the frozen specification is compiled separately.
theorem ekg_exact_counting :
    ∀ u : ℕ, 8 ≤ u →
      (Clock.missingPrimes canonical u).card = (P1 u).card + theta1 u ∧
      (Clock.tickAbove canonical u spanTickValue).card + theta2 u = (P2 u).card ∧
      (P1 u).card + Nat.primeCounting (e u / 2) =
        Nat.primeCounting (e u) + halfPrimeIndicator u ∧
      (P2 u).card + Nat.primeCounting (e u / 3) + halfPrimeIndicator u =
        Nat.primeCounting (e u / 2) ∧
      theta u ≤ 2 ∧ 1 ≤ correction u ∧ correction u ≤ 5 ∧
      (e u : ℤ) - ((u + 1 : ℕ) : ℤ) =
        (Nat.primeCounting (e u) : ℤ) -
          2 * (Nat.primeCounting (e u / 2) : ℤ) +
          (Nat.primeCounting (e u / 3) : ℤ) +
          (H u : ℤ) - (K u : ℤ) - (O u : ℤ) + (correction u : ℤ) := by
  intro u hu
  exact ⟨missingPrimes_card u hu, tickAbove_card_add_theta2 u hu,
    P1_card_primeCounting hu, P2_card_primeCounting hu, theta_le_two u hu,
    (correction_bounds u hu).1, (correction_bounds u hu).2,
    exact_integer_clock u hu⟩

#print axioms ekg_exact_counting
