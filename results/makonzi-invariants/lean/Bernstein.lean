import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic

open scoped BigOperators
open Polynomial

namespace Makonzi
theorem bernstein_zero {K : Type*} [Field K] (c : K) (hc : c ≠ 0) :
    ∀ (n : ℕ) (a : Fin (n+1) → K),
      (∑ j : Fin (n+1), C (a j) * X^(j : ℕ) *
        (X + C c)^(n - (j : ℕ)) : K[X]) = 0 → ∀ j, a j = 0 := by
  intro n
  induction n with
  | zero =>
      intro a h j
      have hj : j = 0 := by
        apply Fin.ext
        have hjlt := j.isLt
        omega
      subst j
      have H := congrArg (Polynomial.eval 0) h
      simpa using H
  | succ n ih =>
      intro a h
      let tail : K[X] := ∑ j : Fin (n+1), C (a j.succ) * X^(j : ℕ) *
        (X + C c)^(n - (j : ℕ))
      have split :
          (∑ j : Fin (n+1+1), C (a j) * X^(j : ℕ) *
            (X + C c)^(n+1 - (j : ℕ)) : K[X]) =
          C (a 0) * (X + C c)^(n+1) + X * tail := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, mul_one, Nat.sub_zero]
        congr 1
        dsimp [tail]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Fin.val_succ, Nat.add_sub_add_right, pow_succ]
        ring
      have H : C (a 0) * (X + C c)^(n+1) + X * tail = 0 := split.symm.trans h
      have h0 : a 0 * c^(n+1) = 0 := by
        have H0 := congrArg (Polynomial.eval 0) H
        simpa using H0
      have ha0 : a 0 = 0 := (mul_eq_zero.mp h0).resolve_right (pow_ne_zero _ hc)
      rw [ha0, map_zero, zero_mul, zero_add] at H
      have ht : tail = 0 := (mul_eq_zero.mp H).resolve_left Polynomial.X_ne_zero
      have hall := ih (fun j => a j.succ) ht
      intro j
      exact Fin.cases ha0 (fun i => hall i) j

#print axioms bernstein_zero
end Makonzi
