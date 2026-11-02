import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
Exact polynomial expansion of the specified height
histogram. This arithmetic module does not assert that the histogram counts
lattice points; the geometric bridge must establish that separately.
-/

namespace BaseREhrhart

/-- The fixed six-bin height histogram, indexed by heights zero through five. -/
def weight : Fin 6 → ℕ := ![1, 8567, 130403, 278187, 114478, 6188]

/-- The number of nonnegative six-coordinate vectors with total `t - h`,
with impossible negative totals excluded explicitly. -/
def binomTerm (t h : ℕ) : ℕ := if h ≤ t then Nat.choose (t - h + 5) 5 else 0

/-- The natural-number count obtained from the fixed histogram. -/
def histogramCount (t : ℕ) : ℕ := ∑ h : Fin 6, weight h * binomTerm t h

/-- The candidate polynomial, interpreted over the rationals. -/
def ehrhartPolynomial (x : ℚ) : ℚ :=
  1 - (268 / 15) * x + (3955 / 12) * x ^ 2 + (5833 / 2) * x ^ 3 +
    (10343 / 12) * x ^ 4 + (67228 / 15) * x ^ 5

lemma choose_five (n : ℕ) :
    ((Nat.choose (n + 5) 5 : ℕ) : ℚ) =
      ((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3) *
        ((n : ℚ) + 4) * ((n : ℚ) + 5) / 120 := by
  have h := congrArg (fun a : ℕ => (a : ℚ))
    (Nat.ascFactorial_eq_factorial_mul_choose n 5)
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial_succ] at h
  apply (eq_div_iff (by norm_num : (120 : ℚ) ≠ 0)).2
  nlinarith [h]

lemma cast_binomTerm (t h : ℕ) (hh : h ≤ t) :
    (binomTerm t h : ℚ) =
      ((t : ℚ) - h + 1) * ((t : ℚ) - h + 2) * ((t : ℚ) - h + 3) *
        ((t : ℚ) - h + 4) * ((t : ℚ) - h + 5) / 120 := by
  rw [binomTerm, if_pos hh, choose_five, Nat.cast_sub hh]

/-- For every natural dilation parameter, the histogram count equals the
stated polynomial; the proof includes the small-parameter truncations. -/
theorem histogramCount_eq_polynomial (t : ℕ) :
    (histogramCount t : ℚ) = ehrhartPolynomial t := by
  by_cases ht : t < 5
  · interval_cases t <;>
      norm_num [histogramCount, binomTerm, weight, Fin.sum_univ_succ, ehrhartPolynomial, Nat.choose]
  · have h5 : 5 ≤ t := by omega
    have h0 : 0 ≤ t := Nat.zero_le t
    have h1 : 1 ≤ t := by omega
    have h2 : 2 ≤ t := by omega
    have h3 : 3 ≤ t := by omega
    have h4 : 4 ≤ t := by omega
    simp [histogramCount, Fin.sum_univ_succ, weight,
      cast_binomTerm, h0, h1, h2, h3, h4, h5, ehrhartPolynomial]
    ring

lemma ehrhartPolynomial_zero : ehrhartPolynomial 0 = 1 := by
  norm_num [ehrhartPolynomial]

lemma linear_coefficient_negative : (-268 / 15 : ℚ) < 0 := by norm_num

end BaseREhrhart
