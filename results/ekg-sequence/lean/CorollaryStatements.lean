import EKG.EndpointDefinitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Statements of the corollaries, fixed independently of their proofs.
`a n` is the one-based EKG sequence A064413: a(1) = 1, a(2) = 2, and each
later term is the least unused positive integer sharing a factor with the
term before it. Logarithms are natural.
-/

open EKG.CanonicalEndpoint Filter Topology

/-- For all sufficiently large n, a(n) < n when a(n) is prime and
a(n) > n when it is not. This is the eventual form of Ordowski's
conjecture on A064413 (2009): if a(n) is not a prime, then a(n) > n. -/
def EventualSignStatement : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ((a n).Prime → a n < n) ∧ (¬ (a n).Prime → n < a n)

/-- Ordowski's density conjecture on A064413 (2009):
#{k ≤ N : a(k) > k} / N tends to 1. -/
def OrdowskiDensityStatement : Prop :=
  Tendsto (fun N : ℕ =>
      ((((Finset.Icc 1 N).filter (fun k => k < a k)).card : ℕ) : ℝ) / (N : ℝ))
    atTop (𝓝 1)

/-- #{k ≤ N : a(k) < k} ~ N / (2 log N). -/
def BelowDiagonalCountStatement : Prop :=
  Tendsto (fun N : ℕ =>
      ((((Finset.Icc 1 N).filter (fun k => a k < k)).card : ℕ) : ℝ) /
        ((N : ℝ) / (2 * Real.log (N : ℝ))))
    atTop (𝓝 1)

/-- Jasinski's conjectures on A152458 and A152519 (2008): each of the three
lines 2 a(k) = k, a(k) = k and 2 a(k) = 3 k holds at only finitely many
indices k. -/
def JasinskiFinitenessStatement : Prop :=
  {k : ℕ | 0 < k ∧ 2 * a k = k}.Finite ∧
  {k : ℕ | 0 < k ∧ a k = k}.Finite ∧
  {k : ℕ | 0 < k ∧ 2 * a k = 3 * k}.Finite

/-- Two related finite sets: Ordowski's exceptional indices A155549
(a(n) not prime and a(n) ≤ n - 1) and A064420 (a(k + 1) = k). -/
def ExceptionalFinitenessStatement : Prop :=
  {n : ℕ | 0 < n ∧ ¬ (a n).Prime ∧ a n ≤ n - 1}.Finite ∧
  {k : ℕ | 0 < k ∧ a (k + 1) = k}.Finite

/-- For each L, the permutation n ↦ a(n) of the positive integers has only
finitely many cycles of length at most L. A cycle is the orbit
{m, a(m), a(a(m)), ...} of a positive integer m with a^[l](m) = m for some
1 ≤ l ≤ L. -/
def ShortCyclesStatement : Prop :=
  ∀ L : ℕ, {C : Set ℕ | ∃ m : ℕ, 0 < m ∧
      (∃ l : ℕ, 0 < l ∧ l ≤ L ∧ a^[l] m = m) ∧
      C = Set.range (fun j : ℕ => a^[j] m)}.Finite
