import ErsConj13.Defs
import ErsConj13.ScatDefs

/-!
# Examples: checks of the definitions

Small checks that the definitions mean what their docstrings say. They are not used by the proof.
-/

namespace ErsConj13

open MvPowerSeries

/-- The bracket on monomials: `{z^a, z^b} = ω(a,b) z^{a+b}`, `ω(a,b) = a₁b₂ − a₂b₁`. -/
theorem bracket_monomial (a b : Fin 2 →₀ ℕ) :
    bracket (monomial a 1) (monomial b 1) =
      monomial (a + b) (((a 0 : ℚ) * b 1 - (a 1 : ℚ) * b 0)) := by
  have hz : ∀ (i : Fin 2) (c : Fin 2 →₀ ℕ),
      zd i (monomial c (1 : ℚ)) = monomial c ((c i : ℚ)) := by
    intro i c; ext e
    show (e i : ℚ) * coeff e (monomial c (1 : ℚ)) = coeff e (monomial c (c i : ℚ))
    rw [coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  simp only [bracket, hz, monomial_mul_monomial]
  rw [← map_sub]

/-- The first values of the conjectured coefficients `a_j` (Elgin–Reading–Stella Conjecture 13:
`a_1, a_2, a_3 = 2, 5, 17` and `a_7 = 4815`). -/
example : ersCoeff 1 = 2 := by norm_num [ersCoeff, Finset.sum_range_succ]
example : ersCoeff 2 = 5 := by norm_num [ersCoeff, Finset.sum_range_succ]
example : ersCoeff 3 = 17 := by norm_num [ersCoeff, Finset.sum_range_succ, Nat.choose]
example : ersCoeff 7 = 4815 := by
  have h : (∑ ℓ ∈ Finset.range 9, Nat.choose ℓ (8 - ℓ) * Nat.choose (6 + ℓ) ℓ) = 33705 := by
    decide
  rw [ersCoeff, show (7 : ℕ) + 2 = 9 by rfl]
  have h' : (∑ ℓ ∈ Finset.range 9, ((Nat.choose ℓ (7 + 1 - ℓ) * Nat.choose (7 + ℓ - 1) ℓ : ℕ) : ℚ))
      = 33705 := by
    rw [← Nat.cast_sum]; exact_mod_cast h
  rw [h']; norm_num

end ErsConj13

/-! Rays and slopes: slope `s = n/d` in lowest terms is the ray `(d, n)`, and `⊤` is `(0, 1)`. -/

namespace ErsConj13.Scat

lemma ray_coe (q : ℚ≥0) : ray (q : Slope) = (q.den, q.num) := rfl
lemma ray_top : ray (⊤ : Slope) = (0, 1) := rfl

example : ray ((1 / 2 : ℚ≥0) : Slope) = (2, 1) := by
  rw [ray_coe, Prod.mk.injEq]
  constructor
  · rw [← NNRat.den_coe]; push_cast; norm_num
  · have h : ((1 / 2 : ℚ≥0) : ℚ).num = 1 := by push_cast; norm_num
    rw [NNRat.num_coe] at h; exact_mod_cast h
example : ray ((0 : ℚ≥0) : Slope) = (1, 0) := by rw [ray_coe]; simp
example : ray ((1 : ℚ≥0) : Slope) = (1, 1) := by rw [ray_coe]; simp
example : slopeOf 2 1 = ((1 / 2 : ℚ≥0) : Slope) := by simp [slopeOf]
example : slopeOf 0 1 = ⊤ := by simp [slopeOf]
example : slopeOf 1 0 = ((0 : ℚ≥0) : Slope) := by simp [slopeOf]

end ErsConj13.Scat
