import Uniform5.CompositionSingleFanCover
import Uniform5.CompositionSphericalPerimeter

/-! Recover polygon-fan membership from actual vertex-figure endpoints.
The three polygon vertices span its affine plane, and an actual face
contains every parent point in its own affine span. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem planar_face_subset_of_three_vertices {P G F : Set E}
    (hG : IsConvexFace P G) (hF : IsConvexFace P F) (hdG : affineDimension G = 2)
    {v a b : E} (hvG : v ∈ G.extremePoints ℝ)
    (haG : a ∈ G.extremePoints ℝ) (hbG : b ∈ G.extremePoints ℝ)
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hvF : v ∈ F) (haF : a ∈ F) (hbF : b ∈ F) : G ⊆ F := by
  have hdir : (affineSpan ℝ G).direction ≤ (affineSpan ℝ F).direction := by
    rw [← planar_three_vertices_span hdG hvG haG hbG hva hvb hab]
    apply Submodule.span_le.mpr
    rintro x (rfl | rfl)
    · exact AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ F haF) (subset_affineSpan ℝ F hvF)
    · exact AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ F hbF) (subset_affineSpan ℝ F hvF)
  intro x hx
  rw [← face_affineSpan_inter hF ⟨v, hvF⟩]
  refine ⟨hG.2.1 hx, ?_⟩
  have hxdir := hdir (AffineSubspace.vsub_mem_direction
    (subset_affineSpan ℝ G hx) (subset_affineSpan ℝ G hvG.1))
  have hh := AffineSubspace.vadd_mem_of_mem_direction hxdir (subset_affineSpan ℝ F hvF)
  simpa only [vsub_vadd] using hh

/-- The same two actual polygon neighbors determine the entire polygon,
not only its section segment. -/
theorem polygonFace_eq_of_common_neighbor_pair {P G H : Set E} {n m : ℕ}
    (hG : PolygonFace P G n) (hH : PolygonFace P H m) {v a b : E}
    (haG : Edge G v a) (hbG : Edge G v b)
    (haH : Edge H v a) (hbH : Edge H v b) (hab : a ≠ b) : G = H := by
  apply Subset.antisymm
  · exact planar_face_subset_of_three_vertices hG.1 hH.1 hG.2.1
      haG.1 haG.2.1 hbG.2.1 haG.2.2.1 hbG.2.2.1 hab
      haH.1.1 haH.2.1.1 hbH.2.1.1
  · exact planar_face_subset_of_three_vertices hH.1 hG.1 hH.2.1
      haH.1 haH.2.1 hbH.2.1 haH.2.2.1 hbH.2.2.1 hab
      haG.1.1 haG.2.1.1 hbG.2.1.1

/-- Every actual VF facet containing both polygon-neighbor endpoints
is the section of a facet in the actual polygon cycle. -/
theorem unitUniform5_figure_facet_in_polygon_fan
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (D : ActualPolygonCycle P G)
    {v a b : Space 5} (haG : Edge G v a) (hbG : Edge G v b) (hab : a ≠ b)
    {F : Set (Space 5)}
    (hF : Facet (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) F)
    (haF : a ∈ F) (hbF : b ∈ F) :
    ∃ i : Fin D.length, F = D.facet i ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) := by
  have hv : v ∈ P.extremePoints ℝ := hG.1.2.extremePoints_subset_extremePoints haG.1
  obtain ⟨K, hK, _, hvK, hKF, _⟩ := unitUniform5_vertexFigure_facet hP hv hF
  have haK : a ∈ K := (hKF.symm ▸ haF).1
  have hbK : b ∈ K := (hKF.symm ▸ hbF).1
  have hGK := planar_face_subset_of_three_vertices hG.1 hK.1 hG.2.1
    haG.1 haG.2.1 hbG.2.1 haG.2.2.1 hbG.2.2.1 hab hvK.1 haK hbK
  obtain ⟨i, hi⟩ := (D.facet_coverage K).mp ⟨hK, hGK⟩
  exact ⟨i, by rw [hi]; exact hKF.symm⟩

end Uniform5.Composition
