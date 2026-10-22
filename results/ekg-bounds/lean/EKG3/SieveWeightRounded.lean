import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient

/-! The computable side of the finite supplement to the analytic lower bound.
It imports only what the definitions need, so that the kernel checks of the
finite range load little besides them. -/
namespace EKG3

/-- An upper bound obtained after scaling the logarithm by a power of 2. -/
def rationalLogUpper (n : ℕ) : ℚ :=
  let k := Nat.log 2 n
  let a := 2^k
  let t : ℚ := ((n : ℚ)-a)/((n : ℚ)+a)
  (k : ℚ)*(693148/1000000) +
    2*(t + t^3/3 + t^5/5 + t^7/(1-t^2))

/-- Integer lower weights avoid large rational denominators in the check. -/
def roundedSieveWeight (n : ℕ) : ℕ :=
  if Squarefree n then 1000000 / n.totient else 0

def roundedSieveSum : ℕ → ℕ
  | 0 => 0
  | n+1 => roundedSieveSum n + roundedSieveWeight (n+1)

/-- A tail-recursive check computes every rounded weight exactly once and
ends at a stated running total, so the finite range is certified in chunks. -/
def finiteSieveCheck : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, total, final => total == final
  | count+1, n, total, final =>
    let next := total + roundedSieveWeight (n+1)
    decide (6 ≤ n+1 → rationalLogUpper (n+2) + 107/100 < (next : ℚ)/1000000) &&
      finiteSieveCheck count (n+1) next final

lemma finiteSieveCheck_final (count n total final : ℕ)
    (htotal : total = roundedSieveSum n) (hcheck : finiteSieveCheck count n total final = true) :
    final = roundedSieveSum (n+count) := by
  induction count generalizing n total with
  | zero =>
    simp only [finiteSieveCheck, beq_iff_eq] at hcheck
    simpa [htotal] using hcheck.symm
  | succ count ih =>
    simp only [finiteSieveCheck, Bool.and_eq_true] at hcheck
    have ht : total + roundedSieveWeight (n+1) = roundedSieveSum (n+1) := by
      simp only [htotal, roundedSieveSum]
    have h := ih (n+1) (total + roundedSieveWeight (n+1)) ht hcheck.2
    rwa [show n+1+count = n+(count+1) by omega] at h

lemma finiteSieveCheck_sound (count n total final : ℕ)
    (htotal : total = roundedSieveSum n) (hcheck : finiteSieveCheck count n total final = true)
    (Q : ℕ) (hnQ : n < Q) (hQ : Q ≤ n+count) (hQ6 : 6 ≤ Q) :
    rationalLogUpper (Q+1) + 107/100 < (roundedSieveSum Q : ℚ)/1000000 := by
  induction count generalizing n total with
  | zero => omega
  | succ count ih =>
    simp only [finiteSieveCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    by_cases hnext : Q = n+1
    · subst Q
      simpa only [htotal, roundedSieveSum] using hcheck.1 hQ6
    · have ht : total + roundedSieveWeight (n+1) = roundedSieveSum (n+1) := by
        simp only [htotal, roundedSieveSum]
      exact ih (n+1) (total + roundedSieveWeight (n+1)) ht hcheck.2 (by omega) (by omega)

end EKG3
