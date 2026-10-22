import P16c.Normalizers

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]

lemma facet_decomposition (a b : K) (ha : a ≠ 0) : F a b ha = AF a b ha ⊔ D a b ha := by
  let g := generators a b ha
  have h₀ : g 0 ∈ F a b ha := Subgroup.subset_closure (by simp [g])
  have h₁ : g 1 ∈ F a b ha := Subgroup.subset_closure (by simp [g])
  have h₂ : g 2 ∈ F a b ha := Subgroup.subset_closure (by simp [g])
  have hT : tGen a b ha ∈ F a b ha :=
    (F a b ha).mul_mem ((F a b ha).mul_mem ((F a b ha).mul_mem h₀ h₁) h₂) h₁
  have hT₂ : t₂Gen a b ha ∈ F a b ha :=
    (F a b ha).mul_mem ((F a b ha).mul_mem h₁ hT) h₁
  have hD : D a b ha ≤ F a b ha := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h₁
    · exact h₂
  have hAF : AF a b ha ≤ F a b ha := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hT
    · exact hT₂
  refine le_antisymm ?_ (sup_le hAF hD)
  have h₁D : g 1 ∈ D a b ha := Subgroup.subset_closure (by simp [g])
  have h₂D : g 2 ∈ D a b ha := Subgroup.subset_closure (by simp [g])
  have hTD : tGen a b ha ∈ AF a b ha := Subgroup.subset_closure (by simp)
  have hInv1 : (g 1)⁻¹ = g 1 := inv_eq_of_mul_eq_one_right (generators_involutive a b ha 1)
  have hInv2 : (g 2)⁻¹ = g 2 := inv_eq_of_mul_eq_one_right (generators_involutive a b ha 2)
  have h0eq : g 0 = tGen a b ha * g 1 * g 2 * g 1 := by
    calc
      g 0 = tGen a b ha * (g 1)⁻¹ * (g 2)⁻¹ * (g 1)⁻¹ := by dsimp [tGen, g]; group
      _ = _ := by rw [hInv1, hInv2]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [show generators a b ha 0 = g 0 from rfl, h0eq]
    exact (AF a b ha ⊔ D a b ha).mul_mem ((AF a b ha ⊔ D a b ha).mul_mem ((AF a b ha ⊔ D a b ha).mul_mem (Subgroup.mem_sup_left hTD)
      (Subgroup.mem_sup_right h₁D)) (Subgroup.mem_sup_right h₂D)) (Subgroup.mem_sup_right h₁D)
  · exact Subgroup.mem_sup_right h₁D
  · exact Subgroup.mem_sup_right h₂D

lemma vertex_decomposition (a b : K) (ha : a ≠ 0) : Ve a b ha = AV a b ha ⊔ D a b ha := by
  let g := generators a b ha
  have h₁ : g 1 ∈ Ve a b ha := Subgroup.subset_closure (by simp [g])
  have h₂ : g 2 ∈ Ve a b ha := Subgroup.subset_closure (by simp [g])
  have h₃ : g 3 ∈ Ve a b ha := Subgroup.subset_closure (by simp [g])
  have hV : vGen a b ha ∈ Ve a b ha :=
    (Ve a b ha).mul_mem ((Ve a b ha).mul_mem ((Ve a b ha).mul_mem h₁ h₂) h₃) h₂
  have hV₂ : v₂Gen a b ha ∈ Ve a b ha :=
    (Ve a b ha).mul_mem ((Ve a b ha).mul_mem h₂ hV) h₂
  have hD : D a b ha ≤ Ve a b ha := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h₁
    · exact h₂
  have hAV : AV a b ha ≤ Ve a b ha := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hV
    · exact hV₂
  refine le_antisymm ?_ (sup_le hAV hD)
  have h₁D : g 1 ∈ D a b ha := Subgroup.subset_closure (by simp [g])
  have h₂D : g 2 ∈ D a b ha := Subgroup.subset_closure (by simp [g])
  have hVD : vGen a b ha ∈ AV a b ha := Subgroup.subset_closure (by simp)
  have hInv1 : (g 1)⁻¹ = g 1 := inv_eq_of_mul_eq_one_right (generators_involutive a b ha 1)
  have hInv2 : (g 2)⁻¹ = g 2 := inv_eq_of_mul_eq_one_right (generators_involutive a b ha 2)
  have h3eq : g 3 = g 2 * g 1 * vGen a b ha * g 2 := by
    calc
      g 3 = (g 2)⁻¹ * (g 1)⁻¹ * vGen a b ha * (g 2)⁻¹ := by dsimp [vGen, g]; group
      _ = _ := by rw [hInv1, hInv2]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.mem_sup_right h₁D
  · exact Subgroup.mem_sup_right h₂D
  · rw [show generators a b ha 3 = g 3 from rfl, h3eq]
    exact (AV a b ha ⊔ D a b ha).mul_mem ((AV a b ha ⊔ D a b ha).mul_mem ((AV a b ha ⊔ D a b ha).mul_mem (Subgroup.mem_sup_right h₂D)
      (Subgroup.mem_sup_right h₁D)) (Subgroup.mem_sup_left hVD)) (Subgroup.mem_sup_right h₂D)
end P16c
