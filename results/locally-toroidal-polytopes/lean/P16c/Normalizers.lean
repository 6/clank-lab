import P16c.Actions

namespace P16c

lemma involution_normalizes_closure {G : Type*} [Group G] (q : G) (hq : q * q = 1)
    (S : Set G) (hS : ∀ x ∈ S, q * x * q ∈ Subgroup.closure S) :
    q ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have hi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  have hconj : ∀ x ∈ Subgroup.closure S, q * x * q ∈ Subgroup.closure S := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hS x hx
    | one => simpa [hq] using (Subgroup.closure S).one_mem
    | mul x y hx hy ihx ihy =>
      have he : q * (x * y) * q = (q * x * q) * (q * y * q) := by simp [mul_assoc, ← mul_assoc q q, hq]
      rw [he]
      exact (Subgroup.closure S).mul_mem ihx ihy
    | inv x hx ih =>
      have he : q * x⁻¹ * q = (q * x * q)⁻¹ := by simp [mul_inv_rev, hi, mul_assoc]
      rw [he]
      exact (Subgroup.closure S).inv_mem ih
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hi]
  refine ⟨hconj x, fun hx => ?_⟩
  simpa [mul_assoc, ← mul_assoc q q, hq] using hconj (q * x * q) hx

variable {K : Type*} [Field K] [CharP K 2]

lemma d_normalizes_af (a b : K) (ha : a ≠ 0) : D a b ha ≤ Subgroup.normalizer (AF a b ha : Set (Mat K)ˣ) := by
  have ht : tGen a b ha ∈ AF a b ha := Subgroup.subset_closure (by simp)
  have ht₂ : t₂Gen a b ha ∈ AF a b ha := Subgroup.subset_closure (by simp)
  apply (Subgroup.closure_le _).mpr
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl
  · apply involution_normalizes_closure _ (generators_involutive a b ha 1)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simpa only [AF, AV, conjugate_t] using ht₂
    · simpa only [AF, AV, conjugate_t₂] using ht
  · apply involution_normalizes_closure _ (generators_involutive a b ha 2)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simpa only [AF, AV, conjugate_t_fixed] using ht
    · simpa only [AF, AV, conjugate_t₂_inv] using (AF a b ha).inv_mem ht₂

lemma d_normalizes_av (a b : K) (ha : a ≠ 0) : D a b ha ≤ Subgroup.normalizer (AV a b ha : Set (Mat K)ˣ) := by
  have hv : vGen a b ha ∈ AV a b ha := Subgroup.subset_closure (by simp)
  have hv₂ : v₂Gen a b ha ∈ AV a b ha := Subgroup.subset_closure (by simp)
  apply (Subgroup.closure_le _).mpr
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl
  · apply involution_normalizes_closure _ (generators_involutive a b ha 1)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simpa only [AF, AV, conjugate_v_inv] using (AV a b ha).inv_mem hv
    · simpa only [AF, AV, conjugate_v₂_fixed] using hv₂
  · apply involution_normalizes_closure _ (generators_involutive a b ha 2)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simpa only [AF, AV, conjugate_v] using hv₂
    · simpa only [AF, AV, conjugate_v₂] using hv
end P16c
