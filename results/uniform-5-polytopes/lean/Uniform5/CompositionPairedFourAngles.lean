import Uniform5.CompositionCaseBCycleTypes

/-! The actual angle budget forces all three small parameters of a
four-slot paired Type I cycle to be three. -/
noncomputable section
namespace Uniform5.Composition
open scoped BigOperators

theorem paired_four_small_parameters {m : ℕ} (hm : m = 4)
    (q : Fin m → ℕ) (hq : ∀ i, 3 ≤ q i) (j : Fin m) (hj : 17 ≤ q j)
    (hangle : (∑ i, (1 - 2 / (q i : ℝ))) < 2) :
    ∀ i : Fin m, i ≠ j → q i = 3 := by
  classical
  intro i hij
  by_contra hne
  have hi : 4 ≤ q i := by have := hq i; omega
  have hjR : (17 : ℝ) ≤ q j := by exact_mod_cast hj
  have hiR : (4 : ℝ) ≤ q i := by exact_mod_cast hi
  have hjA : (15 / 17 : ℝ) ≤ 1 - 2 / q j := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 17) hjR
    linarith
  have hiA : (1 / 2 : ℝ) ≤ 1 - 2 / q i := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 4) hiR
    linarith
  have hb (t : Fin m) :
      (1 / 3 : ℝ) + (if t = j then 28 / 51 else 0) + (if t = i then 1 / 6 else 0) ≤
      1 - 2 / (q t : ℝ) := by
    by_cases htj : t = j
    · subst t
      simp only [ite_true, if_neg hij.symm]
      linarith
    · by_cases hti : t = i
      · subst t
        simp only [if_neg hij, ite_true]
        linarith
      · simp only [if_neg htj, if_neg hti, add_zero]
        exact CaseB.polygon_angle_lower (hq t)
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin m))) => hb t)
  have he : (∑ t : Fin m,
      ((1 / 3 : ℝ) + (if t = j then 28 / 51 else 0) + (if t = i then 1 / 6 else 0))) =
      4 / 3 + 28 / 51 + 1 / 6 := by
    norm_num [Finset.sum_add_distrib, hm]
  rw [he] at hs
  linarith

/-- A paired Type I cycle has only three or four slots. -/
theorem paired_angle_cycle_length {m : ℕ} (hm : 3 ≤ m)
    (q : Fin m → ℕ) (hq : ∀ i, 3 ≤ q i) (j : Fin m) (hj : 17 ≤ q j)
    (hangle : (∑ i, (1 - 2 / (q i : ℝ))) < 2) : m = 3 ∨ m = 4 := by
  classical
  have hjR : (17 : ℝ) ≤ q j := by exact_mod_cast hj
  have hjA : (15 / 17 : ℝ) ≤ 1 - 2 / q j := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 17) hjR
    linarith
  have hb (t : Fin m) : (1 / 3 : ℝ) + (if t = j then 28 / 51 else 0) ≤
      1 - 2 / (q t : ℝ) := by
    by_cases ht : t = j
    · subst t
      simp only [ite_true]
      linarith
    · simp only [if_neg ht, add_zero]
      exact CaseB.polygon_angle_lower (hq t)
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin m))) => hb t)
  have he : (∑ t : Fin m, ((1 / 3 : ℝ) + (if t = j then 28 / 51 else 0))) =
      m / 3 + 28 / 51 := by
    simp [Finset.sum_add_distrib, div_eq_mul_inv]
  rw [he] at hs
  have hm5 : m < 5 := by
    by_contra hh
    have hmR : (5 : ℝ) ≤ m := by exact_mod_cast (show 5 ≤ m by omega)
    linarith
  omega

end Uniform5.Composition
