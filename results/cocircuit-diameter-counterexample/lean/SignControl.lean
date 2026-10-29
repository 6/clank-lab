import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Matrix.Adjugate

/- Quantitative scalar part of the cofactor specialization route.
   This does not assert any determinant coefficient bound or cell cover. -/
namespace ADKZPricing

open Finset

def integerTail (s : Finset ℕ) (c : ℕ → ℤ) (t : ℚ) : ℚ :=
  ∑ k ∈ s, (c k : ℚ) * t ^ (k + 1)

def tailMass (s : Finset ℕ) (c : ℕ → ℤ) : ℚ :=
  ∑ k ∈ s, |(c k : ℚ)|

theorem integer_tail_bound (s : Finset ℕ) (c : ℕ → ℤ) (t : ℚ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |integerTail s c t| ≤ t * tailMass s c := by
  calc
    |integerTail s c t| ≤ ∑ k ∈ s, |(c k : ℚ) * t ^ (k + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, t * |(c k : ℚ)| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (pow_nonneg ht _), pow_succ]
      have hp : t ^ k ≤ 1 := pow_le_one₀ ht ht1
      calc
        |(c k : ℚ)| * (t ^ k * t) = (t * |(c k : ℚ)|) * t ^ k := by ring
        _ ≤ (t * |(c k : ℚ)|) * 1 :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg ht (abs_nonneg _))
        _ = t * |(c k : ℚ)| := mul_one _
    _ = t * tailMass s c := by rw [tailMass, Finset.mul_sum]

/-- A normalized integer polynomial cannot hide a negative constant term
    behind its tail at this explicit bound. Zero constants are allowed. -/
theorem nonnegative_constant_of_nonnegative_eval
    (s : Finset ℕ) (c : ℕ → ℤ) (a : ℤ) (t : ℚ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hsmall : t * tailMass s c < 1)
    (heval : 0 ≤ (a : ℚ) + integerTail s c t) : 0 ≤ a := by
  by_contra h
  have ha : a ≤ -1 := by omega
  have haq : (a : ℚ) ≤ -1 := by exact_mod_cast ha
  have hb := integer_tail_bound s c t ht ht1
  have hu := le_abs_self (integerTail s c t)
  linarith

theorem positive_eval_of_positive_constant
    (s : Finset ℕ) (c : ℕ → ℤ) (a : ℤ) (t : ℚ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hsmall : t * tailMass s c < 1)
    (ha : 0 < a) : 0 < (a : ℚ) + integerTail s c t := by
  have ha1 : 1 ≤ a := ha
  have haq : (1 : ℚ) ≤ a := by exact_mod_cast ha1
  have hb := integer_tail_bound s c t ht ht1
  have hl := neg_abs_le (integerTail s c t)
  linarith

theorem explicit_small_parameter (s : Finset ℕ) (c : ℕ → ℤ) :
    let t : ℚ := 1 / (tailMass s c + 2)
    0 < t ∧ t ≤ 1 ∧ t * tailMass s c < 1 := by
  have hm : 0 ≤ tailMass s c := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hd : 0 < tailMass s c + 2 := by linarith
  dsimp
  constructor
  · exact one_div_pos.mpr hd
  constructor
  · apply (div_le_iff₀ hd).mpr
    linarith
  · rw [one_div_mul_eq_div]
    apply (div_lt_iff₀ hd).mpr
    linarith

/-- The bound applies to an actual integer polynomial, not just a formal
    list of coefficients. It deliberately allows zero constant terms. -/
theorem polynomial_constant_nonnegative (p : Polynomial ℤ) (t : ℚ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hsmall : t * tailMass (range p.natDegree) (fun k => p.coeff (k + 1)) < 1)
    (heval : 0 ≤ p.eval₂ (Int.castRingHom ℚ) t) : 0 ≤ p.coeff 0 := by
  apply nonnegative_constant_of_nonnegative_eval
    (range p.natDegree) (fun k => p.coeff (k + 1)) (p.coeff 0) t ht ht1 hsmall
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ'] at heval
  simpa [integerTail, add_comm] using heval

open Polynomial

/-- A column of the adjugate gives the cofactor kernel of all other rows.
    A nonzero full determinant ensures that this vector is not zero. -/
theorem cofactor_kernel {r : ℕ} (M : Matrix (Fin r) (Fin r) (Polynomial ℤ))
    (b : Fin r) (hdet : M.det ≠ 0) :
    (∀ i, i ≠ b → ∑ j, M i j * M.adjugate j b = 0) ∧
      (∃ j, M.adjugate j b ≠ 0) := by
  constructor
  · intro i hi
    have h := congrArg (fun N : Matrix (Fin r) (Fin r) (Polynomial ℤ) => N i b)
      (Matrix.mul_adjugate M)
    simpa [Matrix.mul_apply, Matrix.one_apply, hi] using h
  · by_contra hn
    push_neg at hn
    have h := congrArg (fun N : Matrix (Fin r) (Fin r) (Polynomial ℤ) => N b b)
      (Matrix.mul_adjugate M)
    simp [Matrix.mul_apply, hn] at h
    exact hdet h.symm

/-- A nonzero polynomial vector has a COMMON power of X that can be
    removed from every coordinate, leaving a nonzero constant vector. -/
theorem normalize_polynomial_vector {r : ℕ} (Z : Fin r → Polynomial ℤ)
    (hZ : ∃ j, Z j ≠ 0) :
    ∃ m : ℕ, ∃ W : Fin r → Polynomial ℤ,
      (∀ j, Z j = X ^ m * W j) ∧ (∃ j, (W j).coeff 0 ≠ 0) := by
  classical
  have h : ∃ m : ℕ, ∃ j, (Z j).coeff m ≠ 0 := by
    by_contra hn
    push_neg at hn
    obtain ⟨j, hj⟩ := hZ
    apply hj
    ext m
    simpa using hn m j
  let m := Nat.find h
  have hdiv : ∀ j, X ^ m ∣ Z j := by
    intro j
    apply Polynomial.X_pow_dvd_iff.mpr
    intro d hd
    by_contra hn
    exact Nat.find_min h hd ⟨j, hn⟩
  choose W hW using hdiv
  refine ⟨m, W, hW, ?_⟩
  obtain ⟨j, hj⟩ := Nat.find_spec h
  refine ⟨j, ?_⟩
  change (Z j).coeff m ≠ 0 at hj
  rw [hW j, Polynomial.coeff_X_pow_mul'] at hj
  simpa using hj

noncomputable def rowPolynomial {n r : ℕ}
    (A D : Fin n → Fin r → ℤ) (W : Fin r → Polynomial ℤ) (i : Fin n) : Polynomial ℤ :=
  ∑ j, (C (A i j) + X * C (D i j)) * W j

theorem rowPolynomial_factor {n r : ℕ}
    (A D : Fin n → Fin r → ℤ) (Z W : Fin r → Polynomial ℤ) (m : ℕ)
    (hfactor : ∀ j, Z j = X ^ m * W j) (i : Fin n) :
    rowPolynomial A D Z i = X ^ m * rowPolynomial A D W i := by
  simp only [rowPolynomial, hfactor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem normalized_kernel_equation {n r : ℕ}
    (A D : Fin n → Fin r → ℤ) (Z W : Fin r → Polynomial ℤ) (m : ℕ)
    (hfactor : ∀ j, Z j = X ^ m * W j) (i : Fin n)
    (hzero : rowPolynomial A D Z i = 0) : rowPolynomial A D W i = 0 := by
  rw [rowPolynomial_factor A D Z W m hfactor i] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ Polynomial.X_ne_zero)

theorem normalized_slack_nonnegative {n r : ℕ}
    (A D : Fin n → Fin r → ℤ) (Z W : Fin r → Polynomial ℤ) (m : ℕ)
    (hfactor : ∀ j, Z j = X ^ m * W j) (i : Fin n) (t : ℚ) (ht : 0 < t)
    (hfeas : 0 ≤ (rowPolynomial A D Z i).eval₂ (Int.castRingHom ℚ) t) :
    0 ≤ (rowPolynomial A D W i).eval₂ (Int.castRingHom ℚ) t := by
  rw [rowPolynomial_factor A D Z W m hfactor i] at hfeas
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hfeas
  exact nonneg_of_mul_nonneg_right hfeas (pow_pos ht m)

theorem rowPolynomial_constant {n r : ℕ}
    (A D : Fin n → Fin r → ℤ) (W : Fin r → Polynomial ℤ) (i : Fin n) :
    (rowPolynomial A D W i).coeff 0 = ∑ j, A i j * (W j).coeff 0 := by
  simp [rowPolynomial, Polynomial.coeff_sum, Polynomial.coeff_mul]

/-- The constant vector of a normalized polynomial kernel is feasible in
    the old signed cone and annihilates every old active row. This is the
    limit step, with explicit slack bounds; it does not manufacture W,
    prove its constant vector nonzero, or establish arrangement regularity. -/
theorem normalized_kernel_limit {n r : ℕ}
    (A D : Fin n → Fin r → ℤ) (W : Fin r → Polynomial ℤ)
    (B : Finset (Fin n)) (t : ℚ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hsmall : ∀ i, t * tailMass (range (rowPolynomial A D W i).natDegree)
      (fun k => (rowPolynomial A D W i).coeff (k + 1)) < 1)
    (hfeas : ∀ i, 0 ≤ (rowPolynomial A D W i).eval₂ (Int.castRingHom ℚ) t)
    (hkernel : ∀ i ∈ B, rowPolynomial A D W i = 0) :
    (∀ i, 0 ≤ ∑ j, A i j * (W j).coeff 0) ∧
      (∀ i ∈ B, ∑ j, A i j * (W j).coeff 0 = 0) := by
  constructor
  · intro i
    rw [← rowPolynomial_constant A D W i]
    exact polynomial_constant_nonnegative _ t ht ht1 (hsmall i) (hfeas i)
  · intro i hi
    rw [← rowPolynomial_constant A D W i, hkernel i hi]
    simp

#print axioms integer_tail_bound
#print axioms nonnegative_constant_of_nonnegative_eval
#print axioms positive_eval_of_positive_constant
#print axioms explicit_small_parameter
#print axioms polynomial_constant_nonnegative
#print axioms normalize_polynomial_vector
#print axioms cofactor_kernel
#print axioms normalized_kernel_equation
#print axioms normalized_slack_nonnegative
#print axioms normalized_kernel_limit

end ADKZPricing
