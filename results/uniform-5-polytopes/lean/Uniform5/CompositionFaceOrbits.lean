import Uniform5.CompositionUniformFaces
import Uniform5.CompositionSymmetry

/-!
# Polygon orbit witnesses at an actual vertex

Every polygon orbit of a vertex-transitive facet has a representative
through each of its vertices. The representative remains an actual polygon
face of the parent polytope. This supplies the geometric witness used in
`lem:filter`, before interpreting its sides as library labels.
-/

noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem polygonFace_image (g : E ≃ᵃⁱ[ℝ] E) {P F : Set E} {k : ℕ}
    (hF : PolygonFace P F k) : PolygonFace (g '' P) (g '' F) k := by
  classical
  refine ⟨isConvexFace_image g hF.1, ?_, ?_⟩
  · simpa only [affineDimension_image] using hF.2.1
  · obtain ⟨V, hV, hk⟩ := hF.2.2
    refine ⟨V.image g, ?_, ?_⟩
    · rw [Finset.coe_image, hV, affineIsometry_image_extremePoints]
    · simpa only [Finset.card_image_of_injective _ g.injective] using hk

/-- Face incidence and the intrinsic vertex count compose exactly. -/
theorem polygonFace_trans {P K G : Set E} {k : ℕ}
    (hK : IsConvexFace P K) (hG : PolygonFace K G k) : PolygonFace P G k :=
  ⟨⟨hG.1.1, hK.2.trans hG.1.2⟩, hG.2⟩

/-- A facet of an all-small polytope has only small polygons as well. -/
theorem smallFaces_face {P F : Set E} (hP : SmallFaces P)
    (hF : IsConvexFace P F) : SmallFaces F :=
  fun _ _ hG => hP _ _ (polygonFace_trans hF hG)

/-- Incidence in a polygon orbit can be moved to an arbitrary actual vertex
of a vertex-transitive polytope. The map preserves the whole polytope. -/
theorem polygon_orbit_through_vertex {P G : Set E} {k : ℕ}
    (hP : FinitePolytope P) (htrans : VertexTransitive P)
    (hG : PolygonFace P G k) {v : E} (hv : v ∈ P.extremePoints ℝ) :
    ∃ g : E ≃ᵃⁱ[ℝ] E, g '' P = P ∧
      PolygonFace P (g '' G) k ∧ v ∈ (g '' G).extremePoints ℝ := by
  have hne : G.Nonempty := by
    by_contra hh
    have he : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hh
    have hd := hG.2.1
    rw [he] at hd
    unfold affineDimension Uniform5.affineDimension at hd
    rw [AffineSubspace.span_empty, AffineSubspace.direction_bot, finrank_bot] at hd
    omega
  obtain ⟨w, hw⟩ := finitePolytope_extremePoints_nonempty (finitePolytope_face hP hG.1 hne)
  have hwP : w ∈ P.extremePoints ℝ := by
    rw [face_extremePoints_eq hG.1] at hw
    exact hw.2
  obtain ⟨g, hg, hgv⟩ := htrans w hwP v hv
  refine ⟨g, hg, ?_, ?_⟩
  · simpa only [hg] using polygonFace_image g hG
  · rw [← affineIsometry_image_extremePoints]
    exact ⟨w, hw, hgv⟩

/-- The actual facet version needed by the closure filter. The symmetry is
of the facet; it is not assumed to preserve the whole parent polytope. -/
theorem unitUniform_facet_polygon_orbit {n k : ℕ} {P K G : Set E}
    (hP : UnitUniform (n + 4) P) (hK : Facet P K)
    (hG : PolygonFace K G k) {v : E} (hv : v ∈ K.extremePoints ℝ) :
    ∃ g : E ≃ᵃⁱ[ℝ] E, g '' K = K ∧ PolygonFace K (g '' G) k ∧
      PolygonFace P (g '' G) k ∧ v ∈ (g '' G).extremePoints ℝ := by
  have hUK : Uniform (n + 3) K := uniform_facets hP.1 hK
  obtain ⟨g, hgK, hgG, hgv⟩ := polygon_orbit_through_vertex
    (uniform_finitePolytope hUK) (uniform_vertexTransitive hUK) hG hv
  refine ⟨g, hgK, hgG, ?_, hgv⟩
  exact polygonFace_trans hK.1 hgG

/-- A large polygon orbit occurs at every vertex of the actual uniform
polytope, not just at the vertex used to exhibit the large face. -/
theorem unitUniform_largeFace_at_vertex {n : ℕ} {P : Set E}
    (hP : UnitUniform (n + 3) P) (hlarge : LargeFace P)
    {v : E} (hv : v ∈ P.extremePoints ℝ) :
    ∃ F k, PolygonFace P F k ∧ 17 ≤ k ∧ v ∈ F.extremePoints ℝ := by
  obtain ⟨G, k, hG, hk⟩ := hlarge
  obtain ⟨g, _, hgG, hgv⟩ := polygon_orbit_through_vertex
    (uniform_finitePolytope hP.1) (uniform_vertexTransitive hP.1) hG hv
  exact ⟨g '' G, k, hgG, hk, hgv⟩

end Uniform5.Composition
