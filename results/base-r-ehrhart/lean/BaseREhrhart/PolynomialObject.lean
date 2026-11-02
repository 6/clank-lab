import BaseREhrhart.Statement
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Coeff

/-! The exact polynomial object and its linear
coefficient. The geometric counting theorem is in Main.lean. -/
noncomputable section
namespace BaseREhrhart

/-- The polynomial expressed as a polynomial object, so the sign claim
is about its coefficient rather than an informal printed expression. -/
def latticePolynomial : Polynomial ℚ :=
  1 + Polynomial.C (-268 / 15) * Polynomial.X +
  Polynomial.C (3955 / 12) * Polynomial.X ^ 2 +
  Polynomial.C (5833 / 2) * Polynomial.X ^ 3 +
  Polynomial.C (10343 / 12) * Polynomial.X ^ 4 +
  Polynomial.C (67228 / 15) * Polynomial.X ^ 5

lemma latticePolynomial_eval (t : ℚ) :
    latticePolynomial.eval t = proposedPolynomial t := by
  simp [latticePolynomial, proposedPolynomial]
  ring


lemma latticePolynomial_linear_coefficient : latticePolynomial.coeff 1 = -268 / 15 := by
  norm_num [latticePolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_one]

lemma latticePolynomial_linear_negative : latticePolynomial.coeff 1 < 0 := by
  rw [latticePolynomial_linear_coefficient]
  norm_num

end BaseREhrhart
