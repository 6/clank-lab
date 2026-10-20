import EKG.CountingMissing
import EKG.CountingTicks

/-! All finite count inputs to the generic signed clock are discharged for
the unchanged canonical sequence. No asymptotic statement is used. -/
namespace EKG.CanonicalCounting

theorem theta1_le_one (u : ℕ) : theta1 u ≤ 1 := by
  classical
  unfold theta1
  split_ifs <;> omega

theorem halfPrimeIndicator_le_one (u : ℕ) : halfPrimeIndicator u ≤ 1 := by
  classical
  unfold halfPrimeIndicator
  split_ifs <;> omega

theorem theta_le_two (u : ℕ) (hu : 8 ≤ u) : theta u ≤ 2 := by
  have h1 := theta1_le_one u
  have h2 := theta2_le_one u hu
  unfold theta
  omega

theorem correction_bounds (u : ℕ) (hu : 8 ≤ u) :
    1 ≤ correction u ∧ correction u ≤ 5 := by
  have ht := theta_le_two u hu
  have hi := halfPrimeIndicator_le_one u
  unfold correction
  omega

theorem exact_integer_clock (u : ℕ) (hu : 8 ≤ u) :
    (e u : ℤ) - ((u + 1 : ℕ) : ℤ) =
      (Nat.primeCounting (e u) : ℤ) -
        2 * (Nat.primeCounting (e u / 2) : ℤ) +
        (Nat.primeCounting (e u / 3) : ℤ) +
        (H u : ℤ) - (K u : ℤ) - (O u : ℤ) + (correction u : ℤ) := by
  have hclock := Clock.clock_identity_from_interval_counts canonical u spanTickValue
    (P1 u).card (P2 u).card (theta1 u) (theta2 u)
    (missingPrimes_card u hu) (tickAbove_card_add_theta2 u hu)
  have h1 := P1_card_primeCounting hu
  have h2 := P2_card_primeCounting hu
  have h1z : ((P1 u).card : ℤ) + (Nat.primeCounting (e u / 2) : ℤ) =
      (Nat.primeCounting (e u) : ℤ) + (halfPrimeIndicator u : ℤ) := by
    exact_mod_cast h1
  have h2z : ((P2 u).card : ℤ) + (Nat.primeCounting (e u / 3) : ℤ) +
      (halfPrimeIndicator u : ℤ) = (Nat.primeCounting (e u / 2) : ℤ) := by
    exact_mod_cast h2
  change (e u : ℤ) - ((u+1 : ℕ) : ℤ) =
    1 + ((P1 u).card : ℤ) - ((P2 u).card : ℤ) +
      (H u : ℤ) - (K u : ℤ) - (O u : ℤ) +
      ((theta1 u + theta2 u : ℕ) : ℤ) at hclock
  simp only [correction, theta, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at *
  omega

end EKG.CanonicalCounting
