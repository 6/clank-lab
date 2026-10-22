import Mathlib
import P16c.StringC

namespace P16c
variable {G : Type*} [Group G]
open scoped Pointwise

/-- Two commuting factorizations with disjoint middle factors have the expected meet. -/
lemma cross_sup_inf (A B C D : Subgroup G) (hAC : A ≤ C) (hDB : D ≤ B)
    (hCB : C ⊓ B = ⊥)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hCD : ∀ c ∈ C, ∀ d ∈ D, Commute c d) :
    (A ⊔ B) ⊓ (C ⊔ D) = A ⊔ D := by
  have hnAB : A ≤ Subgroup.normalizer B := by
    apply Subgroup.le_normalizer_iff.mpr
    intro a ha b hb
    have he : a * b * a⁻¹ = b := by
      rw [(hAB a ha b hb).eq]
      simp [mul_assoc]
    rwa [he]
  have hnCD : C ≤ Subgroup.normalizer D := by
    apply Subgroup.le_normalizer_iff.mpr
    intro c hc d hd
    have he : c * d * c⁻¹ = d := by
      rw [(hCD c hc d hd).eq]
      simp [mul_assoc]
    rwa [he]
  apply le_antisymm
  · intro x hx
    have hxAB : x ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hnAB]
      exact hx.1
    have hxCD : x ∈ (C : Set G) * (D : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right C D hnCD]
      exact hx.2
    obtain ⟨a, ha, b, hb, hab⟩ := hxAB
    obtain ⟨c, hc, d, hd, hcd⟩ := hxCD
    have habcd : a * b = c * d := hab.trans hcd.symm
    have he : c⁻¹ * a = d * b⁻¹ := by
      calc
        c⁻¹ * a = c⁻¹ * (a * b) * b⁻¹ := by group
        _ = c⁻¹ * (c * d) * b⁻¹ := by rw [habcd]
        _ = d * b⁻¹ := by group
    have hi : c⁻¹ * a ∈ C ⊓ B := by
      constructor
      · exact C.mul_mem (C.inv_mem hc) (hAC ha)
      · rw [he]
        exact B.mul_mem (hDB hd) (B.inv_mem hb)
    rw [hCB] at hi
    have hca : c⁻¹ * a = 1 := by simpa using hi
    have hac : a = c := (inv_mul_eq_one.mp hca).symm
    have hbd : b = d := by
      apply mul_left_cancel (a := c)
      simpa only [hac] using habcd
    rw [← hab, hbd]
    exact (A ⊔ D).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hd)
  · apply sup_le
    · exact le_inf le_sup_left (hAC.trans le_sup_left)
    · exact le_inf (hDB.trans le_sup_right) le_sup_right

end P16c
