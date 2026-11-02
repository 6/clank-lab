import BaseREhrhart.Statement
import Mathlib.Tactic

/-! Exact data used by the semantic bridge. -/
open scoped BigOperators
namespace BaseREhrhart

def D : ℕ := 537824

def cNat : Fin 5 → ℕ := ![13, 182, 2548, 35672, 499408]

def height (b : Fin D) : ℕ :=
  (b.val + ∑ i : Fin 5, (cNat i * b.val) % D) / D

lemma D_pos : 0 < D := by decide
lemma cNat_cast (i : Fin 5) : (cNat i : ℤ) = coefficients i := by
  fin_cases i <;> rfl
lemma c_sum : (∑ i : Fin 5, coefficients i) + 1 = (D : ℤ) := by decide
lemma c_nonneg (i : Fin 5) : 0 ≤ coefficients i := by fin_cases i <;> decide

end BaseREhrhart
