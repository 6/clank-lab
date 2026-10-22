/- Adapted from global-soundness/n10/project/Thomson10Soundness/SDP/Summation.lean (supplied accepted N10 port of proof/lean/ThomsonN9/SDP/Summation.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, MIT). -/
import ThomsonN10.Cert.SDP.Basic
import Mathlib.Data.Complex.BigOperators

/-! Independent finite-sum lemmas for factored three-point certificates. -/

namespace ThomsonN10.Cert.SDP
open ThomsonN10 ThomsonN10.Interfaces

open scoped BigOperators

theorem sum_products_eq_sq {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (∑ i, ∑ j, a i * a j) = (∑ i, a i) ^ 2 := by
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem anchored_gram_sum {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (a : ι → ι → ρ → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ r, a i j r * a i k r) =
      ∑ i, ∑ r, (∑ j, a i j r) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, ∑ k, ∑ r, a i j r * a i k r) =
        ∑ j, ∑ r, ∑ k, a i j r * a i k r := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ r, ∑ j, ∑ k, a i j r * a i k r := Finset.sum_comm
    _ = ∑ r, (∑ j, a i j r) ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _
      exact sum_products_eq_sq _

theorem anchored_gram_sum_nonneg {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (a : ι → ι → ρ → ℝ) :
    0 ≤ ∑ i, ∑ j, ∑ k, ∑ r, a i j r * a i k r := by
  rw [anchored_gram_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun r _ => sq_nonneg _

theorem factored_feature_sum_nonneg {ι ρ κ : Type*}
    [Fintype ι] [Fintype ρ] [Fintype κ]
    (b : ρ → κ → ℝ) (a : ι → ι → κ → ℝ) :
    0 ≤ ∑ i, ∑ j, ∑ k, ∑ r,
      (∑ p, b r p * a i j p) * (∑ p, b r p * a i k p) :=
  anchored_gram_sum_nonneg (fun i j r => ∑ p, b r p * a i j p)

theorem complex_gram_sum {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    (∑ i, ∑ j, (z i * star (z j)).re) =
      (∑ i, (z i).re)^2 + (∑ i, (z i).im)^2 := by
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    mul_neg, sub_neg_eq_add, Finset.sum_add_distrib]
  rw [sum_products_eq_sq, sum_products_eq_sq]

theorem complex_gram_sum_nonneg {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, (z i * star (z j)).re := by
  rw [complex_gram_sum]
  positivity

theorem complex_power_recurrence (z : ℂ) (n : ℕ) :
    (z ^ (n+2)).re = 2*z.re*(z^(n+1)).re - Complex.normSq z*(z^n).re := by
  have h : z^(n+2) = ((2*z.re : ℝ) : ℂ)*z^(n+1) -
      (Complex.normSq z : ℂ)*z^n := by
    rw [← Complex.add_conj, ← Complex.mul_conj]
    simp only [pow_succ]
    ring
  apply_fun Complex.re at h
  simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using h

end ThomsonN10.Cert.SDP
