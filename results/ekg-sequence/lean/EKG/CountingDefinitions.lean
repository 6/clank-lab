import EKG.Clock
import EKG.Span

/-! Frozen finite quantities for the canonical exact-counting unit.
The prefix at zero-based `u` has `u+1` entries. These definitions contain
no theorem or assumed cardinal identity. -/
namespace EKG.CanonicalCounting

noncomputable def e (u : ℕ) : ℕ := frontier canonical u

noncomputable def H (u : ℕ) : ℕ := (Clock.holes canonical u).card

noncomputable def K (u : ℕ) : ℕ := earlyEvenCount canonical u

noncomputable def O (u : ℕ) : ℕ :=
  (Clock.nonTickOddAbove canonical u spanTickValue).card

/-- Primes in the half-open real interval `[e/2,e)`. -/
noncomputable def P1 (u : ℕ) : Finset ℕ := by
  classical
  exact ((e u).primesBelow).filter (fun p => e u ≤ 2 * p)

/-- Primes in the open real interval `(e/3,e/2)`. -/
noncomputable def P2 (u : ℕ) : Finset ℕ := by
  classical
  exact ((e u).primesBelow).filter (fun p => e u < 3 * p ∧ 2 * p < e u)

/-- One-based introduction at `t=u+1`, not at `t+1`. -/
noncomputable def theta1 (u : ℕ) : ℕ := by
  classical
  exact if ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 2 * p < e u ∧
    NewPrimeAt canonical u p then 1 else 0

/-- One-based introduction at `t-1` or `t`. -/
noncomputable def lateTickPrimes (u : ℕ) : Finset ℕ := by
  classical
  exact (P2 u).filter (fun p =>
    NewPrimeAt canonical (u - 1) p ∨ NewPrimeAt canonical u p)

noncomputable def theta2 (u : ℕ) : ℕ := (lateTickPrimes u).card

/-- Sum, not union: the same prime may contribute to both terms. -/
noncomputable def theta (u : ℕ) : ℕ := theta1 u + theta2 u

noncomputable def halfPrimeIndicator (u : ℕ) : ℕ :=
  if (e u / 2).Prime then 1 else 0

noncomputable def correction (u : ℕ) : ℕ :=
  1 + theta u + 2 * halfPrimeIndicator u

end EKG.CanonicalCounting
