import StanleySmithForms.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Invariant factors from `A B = 2`, and the counting step for `k = 3`

The first part is the matrix step of the lattice-free argument: if an integer
matrix `A` has an integer partner `B` with `A B = 2`, then every
diagonalization `U A V = diag(d)` by unimodular `U`, `V` (in particular the
Smith normal form) has entries `±1, ±2`, and the number of even entries is the
2-adic valuation of `det A`.

The second part is the final counting step of the `k = 3` classification: a
comparison of two explicit lists of numbers.
-/

namespace StanleySmithForms

open Matrix

/-- A divisor of `2` in `ℤ` is `±1` or `±2`. -/
theorem int_dvd_two {x : ℤ} (h : x ∣ 2) : x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 := by
  have h1 : x ≤ 2 := Int.le_of_dvd (by norm_num) h
  have h2 : -x ≤ 2 := Int.le_of_dvd (by norm_num) ((neg_dvd).2 h)
  have h0 : x ≠ 0 := by rintro rfl; simp at h
  have h3 : -2 ≤ x := by omega
  interval_cases x <;> simp_all

/-- The 2-adic valuation of `±1` is `0` and of `±2` is `1`. -/
theorem padicValInt_two_of_unit_or_two {x : ℤ} (h : x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2) :
    padicValInt 2 x = if 2 ∣ x then 1 else 0 := by
  rcases h with rfl | rfl | rfl | rfl <;> simp [padicValInt]

theorem padicValInt_two_prod {ι : Type*} (d : ι → ℤ) (s : Finset ι)
    (hd : ∀ i, d i = 1 ∨ d i = -1 ∨ d i = 2 ∨ d i = -2) :
    padicValInt 2 (∏ i ∈ s, d i) = (s.filter (fun i => 2 ∣ d i)).card := by
  classical
  have hne : ∀ i, d i ≠ 0 := fun i => by rcases hd i with h | h | h | h <;> rw [h] <;> norm_num
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, padicValInt.mul (hne j) (Finset.prod_ne_zero_iff.2 fun i _ => hne i),
      ih, Finset.filter_insert, padicValInt_two_of_unit_or_two (hd j)]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp [hj]), add_comm]
    · simp

/-- If `A B = 2` for integer matrices, every diagonalization of `A` by unimodular
matrices has entries `±1, ±2`, and the number of its even entries is the 2-adic
valuation of `det A`. -/
theorem invariant_factors_of_mul_eq_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B U V : Matrix ι ι ℤ} {d : ι → ℤ} (hAB : A * B = 2 • 1)
    (hU : IsUnit U.det) (hV : IsUnit V.det) (hd : U * A * V = Matrix.diagonal d) :
    (∀ i, d i = 1 ∨ d i = -1 ∨ d i = 2 ∨ d i = -2) ∧
      (Finset.univ.filter (fun i => 2 ∣ d i)).card = padicValInt 2 A.det := by
  have hC : Matrix.diagonal d * (V⁻¹ * B * U⁻¹) = 2 • 1 := by
    rw [← hd]
    calc U * A * V * (V⁻¹ * B * U⁻¹) = U * (A * (V * V⁻¹) * B) * U⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 2 • 1 := by
          rw [mul_nonsing_inv _ hV, Matrix.mul_one, hAB, Matrix.mul_smul, Matrix.mul_one,
            Matrix.smul_mul, mul_nonsing_inv _ hU]
  have hdiv : ∀ i, d i ∣ 2 := fun i => by
    have := congrFun (congrFun hC i) i
    simp only [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.one_apply_eq] at this
    exact ⟨_, by rw [this]; rfl⟩
  have hd' : ∀ i, d i = 1 ∨ d i = -1 ∨ d i = 2 ∨ d i = -2 := fun i => int_dvd_two (hdiv i)
  refine ⟨hd', ?_⟩
  have hdet := congrArg Matrix.det hd
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  rw [← padicValInt_two_prod d Finset.univ hd', ← hdet]
  rcases Int.isUnit_iff.1 hU with h | h <;> rcases Int.isUnit_iff.1 hV with h' | h' <;>
    simp [h, h', padicValInt]

/-- The witness: every diagonalization of `A` by unimodular matrices has entries
`±1, ±2`, exactly two of them even. -/
theorem witness_factors {U V : Matrix (Fin 6) (Fin 6) ℤ} {d : Fin 6 → ℤ}
    (hU : IsUnit U.det) (hV : IsUnit V.det) (hd : U * A * V = Matrix.diagonal d) :
    (∀ i, d i = 1 ∨ d i = -1 ∨ d i = 2 ∨ d i = -2) ∧
      (Finset.univ.filter (fun i => 2 ∣ d i)).card = 2 := by
  obtain ⟨h1, h2⟩ := invariant_factors_of_mul_eq_two A_mul_B hU hV hd
  refine ⟨h1, ?_⟩
  rw [h2, A_det]
  simp only [padicValInt, Int.reduceNeg, Int.natAbs_neg]
  rw [show (Int.natAbs 4) = 2 ^ 2 by norm_num, padicValNat.prime_pow]

/-- The conjectured `|α_{f-r+1}|` at `k = 3`, as a function of `r`, where `a`
and `b` count the standard tableaux with `3` in cells `(1,3)` and `(3,1)`,
of contents `2` and `-2`. -/
def predFactor (a b r : ℕ) : ℕ :=
  2 ^ ((if r ≤ a then 1 else 0) + (if r ≤ b then 1 else 0))

/-- The actual `r`-th invariant factor of `X₃`, counted from the top: `2` for
the first `a + b`, then `1`. -/
def actFactor (a b r : ℕ) : ℕ :=
  if r ≤ a + b then 2 else 1

/-- The counting step of the `k = 3` classification: with `a + b ≤ f`, the
conjectured and actual lists agree at every `r = 1, …, f` exactly when `a = 0`
or `b = 0`.

Only this arithmetic is formal. Its inputs are written arguments, not
formalized: the tableau facts (in a standard tableau, `3` can occupy only the
cells `(1,2)`, `(2,1)`, `(1,3)`, `(3,1)`, of contents `1, -1, 2, -2`, and each
partial filling of `1, 2, 3` fitting the shape extends to a standard tableau),
which give `predFactor` from the conjecture; and the content spectrum of `X₃`
together with the step from the group ring identity to integer matrices `A`,
`B` with `A B = 2` on a lattice, which give `actFactor` through
`invariant_factors_of_mul_eq_two`.
-/
theorem k3_counting (f a b : ℕ) (hab : a + b ≤ f) :
    (∀ r, 1 ≤ r → r ≤ f → predFactor a b r = actFactor a b r) ↔ (a = 0 ∨ b = 0) := by
  constructor
  · intro h
    by_contra hne
    have ha : 1 ≤ a := by omega
    have hb : 1 ≤ b := by omega
    have h1 := h 1 le_rfl (by omega)
    simp [predFactor, actFactor, ha, hb, show 1 ≤ a + b by omega] at h1
  · rintro (rfl | rfl) r hr _ <;> simp only [predFactor, actFactor] <;> split_ifs <;> simp_all <;> omega

end StanleySmithForms
