import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic

/-!
Uniform pure-power independence for the actual rational variable.  The proof
uses pole induction with an arbitrary polynomial remainder.  It is the same
successive endpoint evaluation as `bernstein_zero`, applied before choosing a
Bernstein coefficient vector; hence no finite bound or index extension is used.
-/
namespace Makonzi
open scoped BigOperators
open Polynomial

noncomputable section
variable {K : Type*} [Field K]

private theorem clear_power (s b u v : RatFunc K) (hv : v ≠ 0)
    (n k : ℕ) (hk : k ≤ n) :
    (s * (b * u / v)^k) * (v^n * u^n) =
      (s * b^k) * u^(n+k) * v^(n-k) := by
  have hn : n = k + (n-k) := (Nat.add_sub_of_le hk).symm
  conv_lhs => rw [hn]
  simp only [div_pow, mul_pow, pow_add]
  field_simp [hv]
  rw [hn]
  simp only [pow_add, Nat.add_sub_cancel_left]
  ring

private def cleared (A B D : K) (n : ℕ) (P : K[X]) (a b : Fin n → K) : K[X] :=
  P * (X^n * (X+C D)^n) +
    (∑ i : Fin n, C (a i * B^(i.val+1)) *
      (X+C D)^(n+(i.val+1)) * X^(n-(i.val+1))) +
    (∑ i : Fin n, C (b i * A^(i.val+1)) *
      X^(n+(i.val+1)) * (X+C D)^(n-(i.val+1)))

private theorem cleared_zero (A B D : K) (n : ℕ) (P : K[X]) (a b : Fin n → K)
    (h : algebraMap K[X] (RatFunc K) P +
      (∑ i : Fin n, RatFunc.C (a i) *
        (RatFunc.C B * (RatFunc.X + RatFunc.C D) / RatFunc.X)^(i.val+1)) +
      (∑ i : Fin n, RatFunc.C (b i) *
        (RatFunc.C A * RatFunc.X / (RatFunc.X + RatFunc.C D))^(i.val+1)) = 0) :
    cleared A B D n P a b = 0 := by
  have ht : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hu : (RatFunc.X + RatFunc.C D : RatFunc K) ≠ 0 := by
    simpa only [map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using
      (RatFunc.algebraMap_ne_zero (monic_X_add_C D).ne_zero)
  apply RatFunc.algebraMap_injective K
  rw [map_zero]
  simp only [cleared, map_add, map_mul, map_sum, map_pow,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  have H := congrArg (fun f : RatFunc K =>
    f * (RatFunc.X^n * (RatFunc.X+RatFunc.C D)^n)) h
  dsimp only at H
  rw [zero_mul] at H
  rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul] at H
  have ha (i : Fin n) :
      RatFunc.C (a i) *
        (RatFunc.C B * (RatFunc.X + RatFunc.C D) / RatFunc.X)^(i.val+1) *
          (RatFunc.X^n * (RatFunc.X+RatFunc.C D)^n) =
        RatFunc.C (a i) * RatFunc.C B^(i.val+1) *
          (RatFunc.X+RatFunc.C D)^(n+(i.val+1)) * RatFunc.X^(n-(i.val+1)) :=
    clear_power _ _ _ _ ht n (i.val+1) (by omega)
  have hb (i : Fin n) :
      RatFunc.C (b i) *
        (RatFunc.C A * RatFunc.X / (RatFunc.X+RatFunc.C D))^(i.val+1) *
          (RatFunc.X^n * (RatFunc.X+RatFunc.C D)^n) =
        RatFunc.C (b i) * RatFunc.C A^(i.val+1) *
          RatFunc.X^(n+(i.val+1)) * (RatFunc.X+RatFunc.C D)^(n-(i.val+1)) := by
    simpa only [mul_comm (RatFunc.X^n) ((RatFunc.X+RatFunc.C D)^n)] using
      (clear_power (RatFunc.C (b i)) (RatFunc.C A) RatFunc.X
        (RatFunc.X+RatFunc.C D) hu n (i.val+1) (by omega))
  simpa only [ha, hb] using H

private theorem zero_high (n m : ℕ) : (0 : K)^(n+1+(m+1)) = 0 :=
  zero_pow (by omega)

private theorem sum_endpoint (n : ℕ) (f : Fin (n+1) → K) (u : K) :
    (∑ i : Fin (n+1), f i * u^(n+1+(i.val+1)) * 0^(n+1-(i.val+1))) =
      f (Fin.last n) * u^(n+1+(n+1)) := by
  rw [Fin.sum_univ_castSucc]
  have hs : (∑ i : Fin n, f i.castSucc * u^(n+1+(i.castSucc.val+1)) *
      0^(n+1-(i.castSucc.val+1))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : n+1-(i.castSucc.val+1) ≠ 0 := by simp only [Fin.coe_castSucc]; omega
    rw [zero_pow hi, mul_zero]
  simp only [hs, Fin.val_last, Nat.sub_self, pow_zero, mul_one, zero_add]

/-- Independence of the two finite pole families modulo arbitrary polynomials.
There is no bound on the degree of the polynomial remainder. -/
theorem pole_powers_independent (A B D : K) (hA : A ≠ 0) (hB : B ≠ 0)
    (hD : D ≠ 0) : ∀ (n : ℕ) (P : K[X]) (a b : Fin n → K),
    algebraMap K[X] (RatFunc K) P +
      (∑ i : Fin n, RatFunc.C (a i) *
        (RatFunc.C B * (RatFunc.X + RatFunc.C D) / RatFunc.X)^(i.val+1)) +
      (∑ i : Fin n, RatFunc.C (b i) *
        (RatFunc.C A * RatFunc.X / (RatFunc.X + RatFunc.C D))^(i.val+1)) = 0 →
    P = 0 ∧ (∀ i, a i = 0) ∧ (∀ i, b i = 0) := by
  intro n
  induction n with
  | zero =>
      intro P a b h
      simp only [Fin.sum_univ_zero, add_zero] at h
      exact ⟨(RatFunc.algebraMap_injective K) (by simpa using h),
        (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩
  | succ n ih =>
      intro P a b h
      have H := cleared_zero A B D (n+1) P a b h
      have ha : a (Fin.last n) = 0 := by
        have H0 := congrArg (Polynomial.eval 0) H
        simp only [cleared, eval_add, eval_mul, eval_pow, eval_X, eval_C,
          eval_finset_sum, eval_zero, zero_add, zero_pow (by omega : n+1 ≠ 0),
          zero_high,
          mul_zero, zero_mul, add_zero] at H0
        rw [sum_endpoint] at H0
        simp only [Finset.sum_const_zero, add_zero] at H0
        exact (mul_eq_zero.mp ((mul_eq_zero.mp H0).resolve_right
          (pow_ne_zero _ hD))).resolve_right (pow_ne_zero _ hB)
      have hb : b (Fin.last n) = 0 := by
        have H0 := congrArg (Polynomial.eval (-D)) H
        simp only [cleared, eval_add, eval_mul, eval_pow, eval_X, eval_C,
          eval_finset_sum, eval_zero, neg_add_cancel,
          zero_pow (by omega : n+1 ≠ 0), zero_high,
          mul_zero, zero_mul, zero_add, add_zero] at H0
        have hs := sum_endpoint n (fun i => b i * A^(i.val+1)) (-D)
        rw [hs] at H0
        simp only [Finset.sum_const_zero, zero_add] at H0
        exact (mul_eq_zero.mp ((mul_eq_zero.mp H0).resolve_right
          (pow_ne_zero _ (neg_ne_zero.mpr hD)))).resolve_right (pow_ne_zero _ hA)
      have hlow : algebraMap K[X] (RatFunc K) P +
          (∑ i : Fin n, RatFunc.C (a i.castSucc) *
            (RatFunc.C B * (RatFunc.X + RatFunc.C D) / RatFunc.X)^(i.val+1)) +
          (∑ i : Fin n, RatFunc.C (b i.castSucc) *
            (RatFunc.C A * RatFunc.X / (RatFunc.X + RatFunc.C D))^(i.val+1)) = 0 := by
        simpa [Fin.sum_univ_castSucc, ha, hb] using h
      obtain ⟨hp, ha0, hb0⟩ := ih P (fun i => a i.castSucc) (fun i => b i.castSucc) hlow
      exact ⟨hp, (fun i => Fin.lastCases ha ha0 i), (fun i => Fin.lastCases hb hb0 i)⟩

/-- The exact finite-positive-power normal-form interface: all fields and all
natural bounds, with no assumptions of linear independence. -/
theorem pure_powers_independent (A B D : K) (hA : A ≠ 0) (hB : B ≠ 0)
    (hD : D ≠ 0) (N : ℕ) (r : K) (a b c : Fin N → K)
    (h : RatFunc.C r +
      (∑ k : Fin N, RatFunc.C (a k) *
        (RatFunc.C B * (RatFunc.X + RatFunc.C D) / RatFunc.X)^(k.val+1)) +
      (∑ k : Fin N, RatFunc.C (b k) *
        (RatFunc.C A * RatFunc.X / (RatFunc.X + RatFunc.C D))^(k.val+1)) +
      (∑ k : Fin N, RatFunc.C (c k) * RatFunc.X^(k.val+1)) = 0) :
    r = 0 ∧ (∀ k, a k = 0) ∧ (∀ k, b k = 0) ∧ (∀ k, c k = 0) := by
  let P : K[X] := C r + ∑ k : Fin N, C (c k) * X^(k.val+1)
  have hP : algebraMap K[X] (RatFunc K) P +
      (∑ k : Fin N, RatFunc.C (a k) *
        (RatFunc.C B * (RatFunc.X + RatFunc.C D) / RatFunc.X)^(k.val+1)) +
      (∑ k : Fin N, RatFunc.C (b k) *
        (RatFunc.C A * RatFunc.X / (RatFunc.X + RatFunc.C D))^(k.val+1)) = 0 := by
    dsimp only [P]
    simp only [map_add, map_sum, map_mul, map_pow, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X]
    linear_combination h
  obtain ⟨hp, ha, hb⟩ := pole_powers_independent A B D hA hB hD N P a b hP
  have hr : r = 0 := by
    have H := congrArg (Polynomial.eval 0) hp
    simpa [P, eval_finset_sum] using H
  refine ⟨hr, ha, hb, ?_⟩
  intro k
  have H := congrArg (fun Q : K[X] => Q.coeff (k.val+1)) hp
  have H' : (∑ x : Fin N, if k = x then c x else 0) = 0 := by
    simpa [P, finset_sum_coeff, coeff_C_mul_X_pow, Fin.ext_iff] using H
  simpa using H'

#print axioms pole_powers_independent
#print axioms pure_powers_independent
end
end Makonzi
