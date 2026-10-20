import Uniform5.CompositionFigureEdgeCycleEmbedding
import Uniform5.CompositionFigureNormalization

/-! Centered four-dimensional edge cycles retain their actual parent
polygon, including its side count through the exact cosine edge length. -/
noncomputable section
namespace Uniform5.Composition
open Set

namespace ActualPolygonCycle

/-- An actual polygon cycle has a centered four-dimensional realization
with the same complete ridge/facet cycle. The integer k is the vertex count
of the original polygon, and determines this very edge's metric length. -/
theorem exists_centered_figureEdgeCycle {P G : Set (Space 5)}
    (D : ActualPolygonCycle P G) (hP : UnitUniform 5 P) {k : ℕ}
    (hG : PolygonFace P G k) {v : Space 5} (hv : v ∈ G.extremePoints ℝ) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    let V := vertexFigure P v c
    let o := c + figureCenter (v - c) (intrinsicRadius P)
    ∃ (f : Space 4 →ᵃⁱ[ℝ] Space 5) (Q : Set (Space 4)) (x y : Space 4)
      (C : ActualEdgeIncidenceCycle Q (segment ℝ x y) D.length),
      f '' Q = V ∧ f 0 = o ∧ Congruent Q V ∧
      FinitePolytope Q ∧ affineDimension Q = 4 ∧
      (0 : Space 4) ∈ intrinsicInterior ℝ Q ∧ affineSpan ℝ Q = ⊤ ∧
      (∀ z ∈ Q.extremePoints ℝ,
        ‖z‖ = Real.sqrt (1 - 1 / (4 * intrinsicRadius P ^ 2))) ∧
      (∀ z ∈ Q.extremePoints ℝ, ∀ w ∈ Q.extremePoints ℝ, z ≠ w → 1 ≤ dist z w) ∧
      Edge Q x y ∧ 3 ≤ k ∧ dist x y = 2 * Real.cos (Real.pi / k) ∧
      f '' segment ℝ x y = G ∩ V ∧
      (∀ i, f '' C.ridge i = D.cell i ∩ V) ∧
      (∀ i, f '' C.facet i = D.facet i ∩ V) := by
  dsimp only
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
  let V := vertexFigure P v c
  have hvP := hG.1.2.extremePoints_subset_extremePoints hv
  obtain ⟨f, Q, him, hf0, hcongr, hQ, hdQ, h0, htop, hext, hrad, hsep⟩ :=
    unitUniform5_vertexFigure_centered_model hP hvP
  obtain ⟨a, b, he, hea, heb, hseg⟩ := unitUniform5_polygon_vertexFigure_edge hP hvP hG hv.1
  have ha : a ∈ f '' Q := him.symm ▸ he.1.1
  have hb : b ∈ f '' Q := him.symm ▸ he.2.1.1
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  have heQ : Edge Q x y := embedding_edge_reflect f (him.symm ▸ he)
  have hlength : dist x y = 2 * Real.cos (Real.pi / k) := by
    have hh := polygonFace_neighbor_chord (n := 2) hP hG hea heb he.2.2.1
    rwa [f.isometry.dist_eq] at hh
  have hsegment : f '' segment ℝ x y = G ∩ V := by
    exact (image_segment ℝ f.toAffineMap x y).trans hseg.symm
  have hpre : f ⁻¹' (G ∩ V) = segment ℝ x y := by
    rw [← hsegment, Set.preimage_image_eq _ f.injective]
  let A := D.figureEdgeCycle hP hG hv
  let C := (A.pullbackOfImage f him).castEdge hpre
  refine ⟨f, Q, x, y, C, him, hf0, hcongr, hQ, hdQ, h0, htop, hrad, hsep,
    heQ, (polygonFace_unitPolygon hP hG).1, hlength, hsegment, ?_, ?_⟩
  · intro i
    change f '' ((A.pullbackOfImage f him).castEdge hpre).ridge i = _
    rw [ActualEdgeIncidenceCycle.castEdge_ridge, ActualEdgeIncidenceCycle.pullbackOfImage_ridge]
    have hh : IsConvexFace (f '' Q) (A.ridge i) := him.symm ▸ A.ridge_face i
    rw [embedding_face_image_preimage f hh]
    rfl
  · intro i
    change f '' ((A.pullbackOfImage f him).castEdge hpre).facet i = _
    rw [ActualEdgeIncidenceCycle.castEdge_facet, ActualEdgeIncidenceCycle.pullbackOfImage_facet]
    have hh : IsConvexFace (f '' Q) (A.facet i) := him.symm ▸ (A.facet_incidence i).1.1
    rw [embedding_face_image_preimage f hh]
    rfl

end ActualPolygonCycle
end Uniform5.Composition
