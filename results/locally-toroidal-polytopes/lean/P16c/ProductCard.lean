import Mathlib

namespace P16c
open scoped Pointwise

/-- Cardinality of a product of disjoint subgroups, with the second normalizing the first. -/
lemma normalized_sup_card {G : Type*} [Group G] (N H : Subgroup G)
    (hnorm : H ≤ Subgroup.normalizer N) (hdis : Disjoint N H) :
    Nat.card (N ⊔ H : Subgroup G) = Nat.card N * Nat.card H := by
  let f : N × H → (N ⊔ H : Subgroup G) :=
    fun p => ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.property p.2.property⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subgroup.mul_injective_of_disjoint hdis
    exact congrArg Subtype.val hpq
  have hs : Function.Surjective f := by
    intro z
    have hz : (z : G) ∈ ((N : Set G) * (H : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N H hnorm]
      exact z.property
    obtain ⟨n, hn, h, hh, heq⟩ := hz
    refine ⟨(⟨n, hn⟩, ⟨h, hh⟩), ?_⟩
    exact Subtype.ext heq
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf, hs⟩).symm).trans (Nat.card_prod N H)
end P16c
