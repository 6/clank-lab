import AdjacencyConverse

namespace ADKZPricing
open Finset
noncomputable section

theorem covector_sign_cases (A : Matrix (Fin 80) (Fin 41) ℚ) (X : SignVector)
    (hx : Covector A X) (i : Fin 80) : X i = -1 ∨ X i = 0 ∨ X i = 1 := by
  obtain ⟨v, hv⟩ := hx
  rw [hv i]
  unfold realSign
  split_ifs <;> simp

theorem compatible_sign_difference (x y : ℤ)
    (hx : x = -1 ∨ x = 0 ∨ x = 1) (hy : y = -1 ∨ y = 0 ∨ y = 1)
    (hc : x = 0 ∨ y = 0 ∨ x = y) :
    |y - x| = (if x = 0 then 1 else 0) + (if y = 0 then 1 else 0) -
      2 * (if x = 0 ∧ y = 0 then 1 else 0) := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> norm_num at *

theorem adjacent_total_variation (A : Matrix (Fin 80) (Fin 41) ℚ) (hu : Uniform A)
    (X Y : SignVector) (he : Adjacent A X Y) : ∑ i, |Y i - X i| = (2 : ℤ) := by
  have hcX : (signZeros X).card = 40 := uniform_cocircuit_zero_count A hu X he.1
  have hcY : (signZeros Y).card = 40 := uniform_cocircuit_zero_count A hu Y he.2.1
  have hcT := adjacent_composition_zero_count A hu X Y he
  have hsum : (∑ i, |Y i - X i|) =
      (∑ i : Fin 80, (if X i = 0 then 1 else 0 : ℤ)) +
      (∑ i : Fin 80, (if Y i = 0 then 1 else 0 : ℤ)) -
      2 * (∑ i : Fin 80, (if compose X Y i = 0 then 1 else 0 : ℤ)) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [compose_zero_iff]
    exact compatible_sign_difference (X i) (Y i) (covector_sign_cases A X he.1.1 i)
      (covector_sign_cases A Y he.2.1.1 i) (commuting_signs_compatible he.2.2.2.1 i)
  have hX : (∑ i : Fin 80, (if X i = 0 then 1 else 0 : ℤ)) = (signZeros X).card := by simp [signZeros]
  have hY : (∑ i : Fin 80, (if Y i = 0 then 1 else 0 : ℤ)) = (signZeros Y).card := by simp [signZeros]
  have hT : (∑ i : Fin 80, (if compose X Y i = 0 then 1 else 0 : ℤ)) =
      (signZeros (compose X Y)).card := by simp [signZeros]
  rw [hsum, hX, hY, hT, hcX, hcY, hcT]
  norm_num

def variation (f : ℕ → ℤ) (L : ℕ) : ℤ := ∑ j ∈ range L, |f (j + 1) - f j|

theorem variation_endpoint_bound (f : ℕ → ℤ) (L : ℕ) : |f L - f 0| ≤ variation f L := by
  induction L with
  | zero => simp [variation]
  | succ L ih =>
    have ht := abs_sub_le (f (L + 1)) (f L) (f 0)
    rw [variation, sum_range_succ]
    change |f (L + 1) - f 0| ≤ variation f L + |f (L + 1) - f L|
    omega

/-- The total variation pays for both sides of ANY visited value. -/
theorem variation_visit_bound (f : ℕ → ℤ) (L j : ℕ) (hj : j ≤ L) :
    |f j - f 0| + |f L - f j| ≤ variation f L := by
  induction L with
  | zero =>
    have he : j = 0 := by omega
    subst j
    simp [variation]
  | succ L ih =>
    by_cases he : j = L + 1
    · subst j
      simpa using variation_endpoint_bound f (L + 1)
    · have hprev := ih (by omega)
      have ht := abs_sub_le (f (L + 1)) (f L) (f j)
      rw [variation, sum_range_succ]
      change |f j - f 0| + |f (L + 1) - f j| ≤ variation f L + |f (L + 1) - f L|
      omega

def visitedNegative (p : ℕ → SignVector) (L : ℕ) : Finset (Fin 80) :=
  univ.filter (fun i => ∃ j, j ≤ L ∧ p j i = -1)

/-- Full-path transition count, including ALL distinct coordinates ever
    negative. It applies to actual full cocircuit adjacency at each step. -/
theorem full_path_transition_count (A : Matrix (Fin 80) (Fin 41) ℚ) (hu : Uniform A)
    (p : ℕ → SignVector) (L : ℕ) (hend : Complementary (p 0) (p L))
    (hedge : ∀ j, j < L → Adjacent A (p j) (p (j + 1))) :
    80 + 2 * (visitedNegative p L).card ≤ 2 * L := by
  classical
  have hcoord : ∀ i : Fin 80, (1 : ℤ) + (if i ∈ visitedNegative p L then 2 else 0) ≤
      variation (fun j => p j i) L := by
    intro i
    by_cases hi : i ∈ visitedNegative p L
    · obtain ⟨j, hj, hneg⟩ := (mem_filter.mp hi).2
      have hb := variation_visit_bound (fun j => p j i) L j hj
      rcases hend.2.2 i with ⟨h0, hL⟩ | ⟨h0, hL⟩ <;>
        simpa [hi, h0, hL, hneg] using hb
    · have hb := variation_endpoint_bound (fun j => p j i) L
      rcases hend.2.2 i with ⟨h0, hL⟩ | ⟨h0, hL⟩ <;>
        simpa [hi, h0, hL] using hb
  have hsum := Finset.sum_le_sum (s := univ) (fun i _ => hcoord i)
  have hleft : (∑ i : Fin 80, ((1 : ℤ) + (if i ∈ visitedNegative p L then 2 else 0))) =
      80 + 2 * ((visitedNegative p L).card : ℤ) := by
    rw [Finset.sum_add_distrib]
    simp
    ring
  have hright : (∑ i : Fin 80, variation (fun j => p j i) L) = 2 * (L : ℤ) := by
    unfold variation
    rw [Finset.sum_comm]
    have heq : (∑ j ∈ range L, ∑ i : Fin 80, |p (j + 1) i - p j i|) =
        ∑ _j ∈ range L, (2 : ℤ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact adjacent_total_variation A hu _ _ (hedge j (mem_range.mp hj))
    rw [heq]
    simp [mul_comm]
  rw [hleft, hright] at hsum
  exact_mod_cast hsum

#print axioms adjacent_total_variation
#print axioms variation_visit_bound
#print axioms full_path_transition_count
end
end ADKZPricing
