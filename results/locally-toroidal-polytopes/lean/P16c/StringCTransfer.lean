import Mathlib
import P16c.StringC

namespace P16c
variable {G H : Type*} [Group G] [Group H]

/-- Taking the subgroup on a generator subset commutes with a homomorphism. -/
lemma parabolic_map {n : ℕ} (g : Fin n → G) (I : Finset (Fin n)) (φ : G →* H) :
    (parabolic g I).map φ = parabolic (fun i => φ (g i)) I := by
  rw [parabolic, MonoidHom.map_closure]
  congr 1
  exact Set.image_image _ _ _

/-- Faithful generator maps reflect the full intersection property. -/
lemma IsStringCGroup.of_injective {n : ℕ} (g : Fin n → G) (φ : G →* H)
    (hφ : Function.Injective φ) (h : IsStringCGroup (fun i => φ (g i))) :
    IsStringCGroup g := by
  refine ⟨fun i => hφ (by simpa using h.1 i), fun i j hij => hφ ?_, ?_⟩
  · simpa using h.2.1 i j hij
  · intro I J
    apply le_antisymm
    · intro x hx
      have hm : φ x ∈ parabolic (fun i => φ (g i)) I ⊓
          parabolic (fun i => φ (g i)) J := by
        constructor
        · rw [← parabolic_map]
          exact ⟨x, hx.1, rfl⟩
        · rw [← parabolic_map]
          exact ⟨x, hx.2, rfl⟩
      change φ x ∈ Subgroup.closure _ ⊓ Subgroup.closure _ at hm
      rw [h.2.2 I J] at hm
      change φ x ∈ parabolic (fun i => φ (g i)) (I ∩ J) at hm
      rw [← parabolic_map] at hm
      obtain ⟨y, hy, he⟩ := hm
      exact hφ he ▸ hy
    · apply le_inf <;> apply Subgroup.closure_mono <;> apply Set.image_mono
      · exact_mod_cast Finset.inter_subset_left
      · exact_mod_cast Finset.inter_subset_right

/-- Every subgroup containing the generators contains each generated subgroup. -/
lemma parabolic_le_of_mem {n : ℕ} (g : Fin n → G) (I : Finset (Fin n))
    (A : Subgroup G) (hg : ∀ i, g i ∈ A) : parabolic g I ≤ A := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, _, rfl⟩
  exact hg i

/-- Faithfulness is needed only on a subgroup containing the generators. -/
lemma IsStringCGroup.of_injOn {n : ℕ} (g : Fin n → G) (φ : G →* H)
    (A : Subgroup G) (hg : ∀ i, g i ∈ A) (hφ : Set.InjOn φ (A : Set G))
    (h : IsStringCGroup (fun i => φ (g i))) : IsStringCGroup g := by
  refine ⟨fun i => hφ (A.pow_mem (hg i) 2) A.one_mem ?_, ?_, ?_⟩
  · simpa using h.1 i
  · intro i j hij
    apply hφ (A.pow_mem (A.mul_mem (hg i) (hg j)) 2) A.one_mem
    simpa using h.2.1 i j hij
  · intro I J
    apply le_antisymm
    · intro x hx
      have hm : φ x ∈ parabolic (fun i => φ (g i)) I ⊓
          parabolic (fun i => φ (g i)) J := by
        constructor
        · rw [← parabolic_map]
          exact ⟨x, hx.1, rfl⟩
        · rw [← parabolic_map]
          exact ⟨x, hx.2, rfl⟩
      change φ x ∈ Subgroup.closure _ ⊓ Subgroup.closure _ at hm
      rw [h.2.2 I J] at hm
      change φ x ∈ parabolic (fun i => φ (g i)) (I ∩ J) at hm
      rw [← parabolic_map] at hm
      obtain ⟨y, hy, he⟩ := hm
      exact hφ (parabolic_le_of_mem g _ A hg hy)
        (parabolic_le_of_mem g _ A hg hx.1) he ▸ hy
    · apply le_inf <;> apply Subgroup.closure_mono <;> apply Set.image_mono
      · exact_mod_cast Finset.inter_subset_left
      · exact_mod_cast Finset.inter_subset_right

/-- A faithful restriction to the left subgroup reflects an intersection equality.
The homomorphism need not be faithful on the ambient group. -/
lemma inf_eq_of_map_inf_eq (φ : G →* H) (A B C : Subgroup G)
    (hCA : C ≤ A) (hCB : C ≤ B)
    (hinj : Set.InjOn φ (A : Set G))
    (hmap : A.map φ ⊓ B.map φ = C.map φ) : A ⊓ B = C := by
  apply le_antisymm
  · intro x hx
    have hi : φ x ∈ A.map φ ⊓ B.map φ :=
      ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
    rw [hmap] at hi
    obtain ⟨y, hy, he⟩ := hi
    exact hinj (hCA hy) hx.1 he ▸ hy
  · exact le_inf hCA hCB

end P16c
