import Uniform5.CompositionFacetSystemGeneral
import Uniform5.CompositionRidgeIncidence

/-! Exact planar neighbor exhaustion from the proved ridge theorem. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem edge_other_endpoint_eq_of_segment_eq {P : Set E} {v a b : E}
    (ha : Edge P v a) (hb : Edge P v b)
    (he : segment ℝ v a = segment ℝ v b) : a = b := by
  have hm : a ∈ segment ℝ v b := he ▸ right_mem_segment ℝ v a
  have hh := (mem_extremePoints_iff_forall_segment.mp ha.2.1).2 v ha.1.1 b hb.2.1.1 hm
  exact (hh.resolve_left ha.2.2.1).symm

/-- In an actual two-dimensional polytope, any two distinct known edge
neighbors exhaust all neighbors. The two incident facets of the singleton
vertex are obtained from the generic codimension-two theorem. -/
theorem finitePolytope_planar_neighbors {P : Set E} (hP : FinitePolytope P)
    (hd : affineDimension P = 2) {v a b : E}
    (ha : Edge P v a) (hb : Edge P v b) (hab : a ≠ b) :
    ∀ z, Edge P v z ↔ z = a ∨ z = b := by
  have hvF : IsConvexFace P {v} := (singleton_face_iff_extremePoint P v).mpr ha.1
  obtain ⟨F, H, hFH, hcover⟩ := finitePolytope_ridge_two_facets hP hvF
    (singleton_nonempty v) (by rw [affineDimension_singleton, hd])
  have hseg {z : E} (hz : Edge P v z) :
      segment ℝ v z = F ∨ segment ℝ v z = H := by
    apply (hcover _).mp
    refine ⟨⟨⟨convex_segment _ _, hz.2.2.2.isExtreme⟩,
      ⟨v, left_mem_segment ℝ _ _⟩, ?_⟩, ?_⟩
    · rw [affineDimension_segment hz.2.2.1, hd]
    · exact singleton_subset_iff.mpr (left_mem_segment ℝ v z)
  have hne : segment ℝ v a ≠ segment ℝ v b :=
    fun h => hab (edge_other_endpoint_eq_of_segment_eq ha hb h)
  intro z
  constructor
  · intro hz
    have haz : segment ℝ v z = segment ℝ v a ∨ segment ℝ v z = segment ℝ v b := by
      rcases hseg ha with ha' | ha' <;> rcases hseg hb with hb' | hb' <;>
        rcases hseg hz with hz' | hz'
      all_goals first
        | exact Or.inl (hz'.trans ha'.symm)
        | exact Or.inr (hz'.trans hb'.symm)
        | exact False.elim (hne (ha'.trans hb'.symm))
    exact haz.elim
      (fun h => Or.inl (edge_other_endpoint_eq_of_segment_eq hz ha h))
      (fun h => Or.inr (edge_other_endpoint_eq_of_segment_eq hz hb h))
  · rintro (rfl | rfl) <;> assumption

end Uniform5.Composition
