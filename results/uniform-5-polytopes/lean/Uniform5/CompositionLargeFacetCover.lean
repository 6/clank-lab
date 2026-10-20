import Uniform5.CompositionCaseBTypeIIIRadius
import Uniform5.CompositionCanonicalCoverage
import Uniform5.CompositionFigureRidgeCorrespondence

/-! The geometric B2 corollary: every polygon lies in a large facet, and
every actual vertex-figure edge belongs to the fan of a large polygon.
The local Omega argument and all three actual radius types are composed. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_polygon_in_large_facet
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) (hlarge : LargeFace P)
    {k : ℕ} (hG : PolygonFace P G k) :
    ∃ K, Facet P K ∧ G ⊆ K ∧ LargeFace K := by
  classical
  obtain ⟨L, n, hL, hn⟩ := hlarge
  have hout := unitUniform5_largePolygon_radius_not_mem classification4D hB2 hP hL hn
  by_cases hk : k ≤ 16
  · by_contra hnone
    have hlocal : ∀ K, Facet P K → G ⊆ K → SmallFaces K := by
      intro K hK hGK
      rcases smallFaces_or_largeFace K with hsmall | hlarge
      · exact hsmall
      · exact (hnone ⟨K, hK, hGK, hlarge⟩).elim
    exact hout (unitUniform5_local_smallFacets_radius_mem_omega
      classification3D classification4D hP hG hk hlocal N S hLIB hS1)
  · obtain ⟨D, _⟩ := unitUniform5_stage1_geometry hP hG
    let i : Fin D.length := ⟨0, by have := D.length_ge; omega⟩
    obtain ⟨hK, hGK, _⟩ := D.facet_incidence i
    refine ⟨D.facet i, hK, hGK, G, k, ?_, by omega⟩
    exact polygonFace_restrict_parent hG hK.1.2.1 hGK

/-- Each actual vertex-figure edge lies in a facet of the fan of some
large polygon through the apex. The large polygon is an actual face of P,
not merely a polygon in a congruent model. -/
theorem unitUniform5_figure_edge_in_large_fan
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hlarge : LargeFace P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) {x y : Space 5}
    (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y) :
    let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    ∃ K, Facet P K ∧ v ∈ K ∧ Facet V (K ∩ V) ∧ segment ℝ x y ⊆ K ∩ V ∧
      ∃ F n, PolygonFace P F n ∧ 17 ≤ n ∧ v ∈ F.extremePoints ℝ ∧ F ⊆ K := by
  dsimp only
  obtain ⟨G, k, hG, hvG, _, _, _, hsection⟩ :=
    unitUniform5_vertexFigure_edge_polygon hP hv he
  obtain ⟨K, hK, hGK, L, n, hL, hn⟩ := unitUniform5_polygon_in_large_facet
    classification3D classification4D N S hLIB hS1 hB2 hP hlarge hG
  have hvK : v ∈ K := hGK hvG
  have hvKe : v ∈ K.extremePoints ℝ := by
    rw [face_extremePoints_eq hK.1]
    exact ⟨hvK, hv⟩
  obtain ⟨g, _, hLK, hLP, hvg⟩ := unitUniform_facet_polygon_orbit hP hK hL hvKe
  refine ⟨K, hK, hvK,
    (unitUniform_vertexFigure_facet_correspondence (n := 2) hP hv).1 K hK hvK, ?_,
    g '' L, n, hLP, hn, hvg, hLK.1.2.1⟩
  rw [← hsection]
  exact inter_subset_inter_left _ hGK

end Uniform5.Composition
