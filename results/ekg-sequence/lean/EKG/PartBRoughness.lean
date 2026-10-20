import EKG.HoleCounting
import EKG.Asymptotic

/-!
Canonical missing-composite roughness at an earlier post-occurrence prefix.
The current upper value `e` is used only to majorize the counting factor;
the displacement remains measured from the actual earlier frontier.
No sharp rate or prime number theorem is used.
-/

namespace EKG.PartB

open Real Filter

/-- The old canonical hole estimate, with its counting factor measured at
any upper value `e`. Both subtractions in the conclusion are real. -/
theorem canonical_missing_composite_upper_bound {i u e : ℕ}
    (hi : 8 ≤ i) (hu : 1 < u) (hnp : ¬ u.Prime)
    (hbelow : u < frontier canonical i)
    (hfree : ¬ UsedBefore canonical.a (i + 1) u) (hue : u ≤ e) :
    (frontier canonical i : ℝ) - (u : ℝ) ≤
      2 * (u.minFac : ℝ) * (13 * Nat.primeCounting (Nat.sqrt e) + 724 : ℕ) := by
  have h15 := HoleCounting.missing_composite_ge_fifteen canonical
    hi hu hnp hbelow hfree
  have hbase := canonical.missing_composite_bound h15 hnp hbelow hfree
  have hpi : Nat.primeCounting (Nat.sqrt u) ≤ Nat.primeCounting (Nat.sqrt e) :=
    Nat.monotone_primeCounting (Nat.sqrt_le_sqrt hue)
  have hcount : 13 * Nat.primeCounting (Nat.sqrt u) + 724 ≤
      13 * Nat.primeCounting (Nat.sqrt e) + 724 := by omega
  have hnat : frontier canonical i - u ≤
      2 * u.minFac * (13 * Nat.primeCounting (Nat.sqrt e) + 724) :=
    hbase.trans (Nat.mul_le_mul_left (2 * u.minFac) hcount)
  have hreal : ((frontier canonical i - u : ℕ) : ℝ) ≤
      ((2 * u.minFac * (13 * Nat.primeCounting (Nat.sqrt e) + 724) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [Nat.cast_sub hbelow.le] at hreal
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hreal

/-- Large real displacement forces every prime factor to be large, even
when the missing value is tested at a historical prefix. The prime in this
conclusion is not identified with the fixed least factor of another hole. -/
theorem canonical_missing_composite_rough {i u e : ℕ} {B : ℝ}
    (hi : 8 ≤ i) (hu : 1 < u) (hnp : ¬ u.Prime)
    (hbelow : u < frontier canonical i)
    (hfree : ¬ UsedBefore canonical.a (i + 1) u) (hue : u ≤ e)
    (hgap : 2 * B * (13 * Nat.primeCounting (Nat.sqrt e) + 724 : ℕ) <
      (frontier canonical i : ℝ) - (u : ℝ)) :
    ∀ p : ℕ, p.Prime → p ∣ u → B < (p : ℝ) := by
  have hbound := canonical_missing_composite_upper_bound hi hu hnp hbelow hfree hue
  intro p hp hpd
  have hmin : u.minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le hpd
  have hminreal : (u.minFac : ℝ) ≤ (p : ℝ) := by exact_mod_cast hmin
  by_contra h
  have hpB : (p : ℝ) ≤ B := le_of_not_gt h
  have hmul := mul_le_mul_of_nonneg_right (hminreal.trans hpB)
    (show (0 : ℝ) ≤ (13 * Nat.primeCounting (Nat.sqrt e) + 724 : ℕ) by positivity)
  nlinarith only [hbound, hgap, hmul]

/-- Geometry of the original missing composite: its fixed least prime
factor is prime, divides it, has square at most the hole, and controls the
real displacement with the same uniform counting factor. -/
theorem canonical_missing_composite_geometry {t h e : ℕ}
    (ht : 8 ≤ t) (hh : 1 < h) (hnp : ¬ h.Prime)
    (hbelow : h < frontier canonical t)
    (hfree : ¬ UsedBefore canonical.a (t + 1) h) (hhe : h ≤ e) :
    h.minFac.Prime ∧ h.minFac ∣ h ∧ h.minFac ^ 2 ≤ h ∧
      (frontier canonical t : ℝ) - (h : ℝ) ≤
        2 * (h.minFac : ℝ) * (13 * Nat.primeCounting (Nat.sqrt e) + 724 : ℕ) := by
  refine ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd h,
    Nat.minFac_sq_le_self (by omega) hnp, ?_⟩
  exact canonical_missing_composite_upper_bound ht hh hnp hbelow hfree hhe

/-- Elementary real majorant for the missing-composite counting factor.
The constant 802 is `13*6+724`, using only the old elementary prime bound. -/
theorem eventually_hole_factor_count_real :
    ∀ᶠ x : ℝ in atTop,
      13 * sqrtPrimeCount x + 724 ≤ 802 * sqrtLogRate x := by
  filter_upwards [eventually_sqrtPrimeCount_le, eventually_one_le_sqrtLogRate]
    with x hp hr
  linarith

/-- The exact natural prime-count expression has the same eventual bound. -/
theorem eventually_hole_factor_count :
    ∀ᶠ e : ℕ in atTop,
      ((13 * Nat.primeCounting (Nat.sqrt e) + 724 : ℕ) : ℝ) ≤
        802 * sqrtLogRate (e : ℝ) := by
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun e : ℕ => (e : ℝ)) atTop atTop).eventually
      eventually_hole_factor_count_real
  filter_upwards [h] with e he
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, primeCounting_sqrt_nat_eq]
    using he

/-- Uniform specialization at the current canonical frontier. -/
theorem eventually_canonical_hole_factor_count :
    ∀ᶠ t : ℕ in atTop,
      ((13 * Nat.primeCounting (Nat.sqrt (frontier canonical t)) + 724 : ℕ) : ℝ) ≤
        802 * sqrtLogRate (frontier canonical t : ℝ) :=
  (frontier_tendsto_atTop canonical).eventually eventually_hole_factor_count

end EKG.PartB
