import Mathlib.Data.Nat.Prime.Basic

namespace Donkin
/-- Product of the first k+1 terms, with zero-based k. -/
def productState (p : ℕ) : ℕ → ℕ
  | 0 => p
  | k + 1 => productState p k * (productState p k + 1).minFac

/-- Zero-based terms: term p 0 is the prime seed. -/
def term (p : ℕ) : ℕ → ℕ
  | 0 => p
  | k + 1 => (productState p k + 1).minFac

/-- Source-faithful endpoint statement only; no proof is asserted. -/
def ArbitraryDelay : Prop :=
  ∀ n : ℕ, 0 < n → ∃ p : ℕ, p.Prime ∧ ∀ j : ℕ, j < n → term p j ≠ 3
end Donkin
