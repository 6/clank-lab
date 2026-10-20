import Uniform5.CompositionFacetContainment

/-! Actual exposed edges, their dimensions, and inheritance through faces. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem affineDimension_segment {v w : E} (hvw : v ≠ w) :
    affineDimension (segment ℝ v w) = 1 := by
  unfold affineDimension Uniform5.affineDimension
  rw [← convexHull_pair, affineSpan_convexHull, direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (sub_ne_zero.mpr hvw)

theorem edge_isConvexFace {P : Set E} {v w : E} (h : Edge P v w) :
    IsConvexFace P (segment ℝ v w) := ⟨convex_segment v w, h.2.2.2.isExtreme⟩

theorem edge_dimension {P : Set E} {v w : E} (h : Edge P v w) :
    affineDimension (segment ℝ v w) = 1 := affineDimension_segment h.2.2.1

theorem edge_proper {P : Set E} {v w : E} (h : Edge P v w)
    (hdim : 1 < affineDimension P) : segment ℝ v w ≠ P := by
  intro heq
  have hd := edge_dimension h
  rw [heq] at hd
  omega

/-- The finite-polytope exposure bridge required by the original face
lemmas now follows from actual geometry. -/
theorem finitePolytope_polytopeFacesExposed [FiniteDimensional ℝ E]
    (V : Finset E) : PolytopeFacesExposed V := by
  intro F hF
  by_cases hV : V.Nonempty
  · exact finitePolytope_face_isExposed ⟨V, hV, rfl⟩ hF
  · have he : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
    have hsub := hF.2.1
    simp only [he, Finset.coe_empty, convexHull_empty, Set.subset_empty_iff] at hsub
    subst F
    exact isExposed_empty

/-- Actual edges inherit in both directions across an actual geometric
face; the formerly separate exposure premise is discharged. -/
theorem edge_face_iff [FiniteDimensional ℝ E] {P F : Set E}
    (hP : FinitePolytope P) (hF : IsConvexFace P F)
    {v w : E} (hv : v ∈ F) (hw : w ∈ F) :
    Edge P v w ↔ Edge F v w := by
  constructor
  · intro h
    refine ⟨?_, ?_, h.2.2.1, h.2.2.2.mono hF.2.1 (hF.1.segment_subset hv hw)⟩
    · rw [face_extremePoints_eq hF]
      exact ⟨hv, h.1⟩
    · rw [face_extremePoints_eq hF]
      exact ⟨hw, h.2.1⟩
  · intro h
    refine ⟨hF.2.extremePoints_subset_extremePoints h.1,
      hF.2.extremePoints_subset_extremePoints h.2.1, h.2.2.1, ?_⟩
    exact finitePolytope_face_isExposed hP (face_of_face hF (edge_isConvexFace h))

/-- Unit-edge normalization descends to every actual face. -/
theorem unitEdges_face [FiniteDimensional ℝ E] {P F : Set E}
    (hP : FinitePolytope P) (hF : IsConvexFace P F) (hunit : UnitEdges P) :
    UnitEdges F := by
  intro v w hvw
  exact hunit v w ((edge_face_iff hP hF hvw.1.1 hvw.2.1.1).mpr hvw)

/-- Every edge of a polytope of dimension at least two is contained in
an actual codimension-one facet. -/
theorem edge_mem_facet [FiniteDimensional ℝ E] {P : Set E}
    (hP : FinitePolytope P) {v w : E} (he : Edge P v w)
    (hdim : 1 < affineDimension P) :
    ∃ F, Facet P F ∧ v ∈ F ∧ w ∈ F := by
  obtain ⟨F, hF, hsub⟩ := finitePolytope_face_subset_facet hP
    (edge_isConvexFace he) ⟨v, left_mem_segment ℝ v w⟩ (edge_proper he hdim)
  exact ⟨F, hF, hsub (left_mem_segment ℝ v w), hsub (right_mem_segment ℝ v w)⟩

/-- Facets inherit both recursive uniformity and the actual edge length. -/
theorem unitUniform_facet [FiniteDimensional ℝ E] {n : ℕ} {P F : Set E}
    (hP : UnitUniform (n + 3) P) (hF : Facet P F) : UnitUniform (n + 2) F :=
  ⟨uniform_facets hP.1 hF,
    unitEdges_face (uniform_finitePolytope hP.1) hF.1 hP.2⟩

end Uniform5.Composition
