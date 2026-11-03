import UniformEndpoint
import Probability

/-! The conditional tie-breaking kernels are probability laws. -/
namespace ADG.Uniform
open Finset
open scoped Classical

theorem countProb_nonneg {m n : ℕ} (A : Matrix m n) (fuel : ℕ)
    (U : Finset (Fin m)) (event : ℕ → Prop) : 0 ≤ countProb A fuel U event := by
  induction fuel generalizing U event with
  | zero => simp only [countProb]; split_ifs <;> norm_num
  | succ fuel ih =>
    rw [countProb]
    by_cases hJ : maximizers A U = ∅
    · rw [if_pos hJ]; split_ifs <;> norm_num
    · rw [if_neg hJ]
      exact div_nonneg (sum_nonneg (fun j _ => ih _ _)) (Nat.cast_nonneg _)

theorem countProb_mono {m n : ℕ} (A : Matrix m n) (fuel : ℕ)
    (U : Finset (Fin m)) (e f : ℕ → Prop) (hef : ∀ g, e g → f g) :
    countProb A fuel U e ≤ countProb A fuel U f := by
  have hi (g : ℕ) : (if e g then (1 : ℝ) else 0) ≤ (if f g then 1 else 0) := by
    by_cases he : e g
    · simp [he, hef g he]
    · simp only [if_neg he]; split_ifs <;> norm_num
  induction fuel generalizing U e f with
  | zero => exact hi 0
  | succ fuel ih =>
    simp only [countProb]
    by_cases hJ : maximizers A U = ∅
    · rw [if_pos hJ, if_pos hJ]; exact hi 0
    · rw [if_neg hJ, if_neg hJ]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact sum_le_sum (fun j _ => ih _ _ _ (fun g => hef (g+1))
        (fun g => hi (g+1)))

theorem countProb_congr {m n : ℕ} (A : Matrix m n) (fuel : ℕ)
    (U : Finset (Fin m)) (e f : ℕ → Prop) (h : ∀ g, e g ↔ f g) :
    countProb A fuel U e = countProb A fuel U f :=
  le_antisymm (countProb_mono A fuel U e f (fun g => (h g).mp))
    (countProb_mono A fuel U f e (fun g => (h g).mpr))

theorem countProb_false {m n : ℕ} (A : Matrix m n) (fuel : ℕ)
    (U : Finset (Fin m)) : countProb A fuel U (fun _ => False) = 0 := by
  induction fuel generalizing U with
  | zero => simp [countProb]
  | succ fuel ih =>
    simp only [countProb]
    by_cases hJ : maximizers A U = ∅
    · simp [hJ]
    · rw [if_neg hJ]
      have he (j : Fin n) : countProb A fuel (U \ A j) (fun g => False) = 0 := ih _
      simp only [he, sum_const_zero, zero_div]

theorem countProb_true {m n : ℕ} (A : Matrix m n) (fuel : ℕ)
    (U : Finset (Fin m)) : countProb A fuel U (fun _ => True) = 1 := by
  induction fuel generalizing U with
  | zero => simp [countProb]
  | succ fuel ih =>
    simp only [countProb]
    split_ifs with hJ
    · simp
    · simp_rw [ih]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      exact div_self (by exact_mod_cast card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hJ))

theorem countProb_le_one {m n : ℕ} (A : Matrix m n) (fuel : ℕ)
    (U : Finset (Fin m)) (event : ℕ → Prop) : countProb A fuel U event ≤ 1 := by
  rw [← countProb_true A fuel U]
  exact countProb_mono A fuel U event (fun _ => True) (fun _ _ => trivial)

theorem jointProb_mono (m n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (e f : Matrix m n → ℕ → Prop) (hef : ∀ A g, e A g → f A g) :
    jointProb m n p e ≤ jointProb m n p f := by
  apply sum_le_sum
  intro A _
  apply mul_le_mul_of_nonneg_left (countProb_mono A m univ _ _ (hef A))
  exact iidMass_nonneg _ (columnMass_nonneg m p hp hp') A

end ADG.Uniform
