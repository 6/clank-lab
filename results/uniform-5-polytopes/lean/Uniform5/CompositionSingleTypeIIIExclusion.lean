import Uniform5.CompositionTypeIIIFanFacetEdges

/-! The actual single-large-polygon Type III branch is impossible. All
fan geometry and its complete seven-vertex edge graph are constructed
from the actual polygon cycle; none is an additional branch premise. -/
noncomputable section
namespace Uniform5.Composition
open Set

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

theorem typeIII_single_impossible
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    {v : Space 5} (hv : v ∈ G.extremePoints ℝ) (hu : UniqueLargeFaceAt P v G)
    (hIII : D.CaseBTypeIII n) : False := by
  obtain ⟨T⟩ := D.typeIII_actual_fan hP hG hn hv hIII
  let hPP := uniform_finitePolytope hP.1
  let c := vertexCentroid (vertices P hPP)
  let Q := vertexFigure P v c
  have hvP := hG.1.2.extremePoints_subset_extremePoints hv
  obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical hPP (uniform_vertexTransitive hP.1)
  have hQ : FinitePolytope Q := finitePolytope_vertexFigure_of_positiveDimension
    hPP hvP c R hs hP.2 (by rw [uniform_dimension hP.1]; norm_num)
  have hself : P ∩ Q = Q := Set.inter_eq_right.mpr (fun _ hx => hx.1)
  have hdQ : affineDimension Q = 4 := by
    have hh := (unitUniform_vertexFigure_face_correspondence (n := 2) hP hvP 4).1 P
      (finitePolytope_self_face hPP) hvP.1 (by simpa using uniform_dimension hP.1)
    have hh' : affineDimension (P ∩ Q) = 4 := hh.2.2
    rwa [hself] at hh'
  apply finitePolytope_seven_vertex_fan_impossible hQ hdQ T.points
    (T.points_injective hG (by omega))
    (T.points_range classification3D classification4D N S hLIB hS1 hB2 hP hG hn hv hu)
    (T.figureFacet hP) ?_ ?_ (T.figureFacet_edges hP hG hn hv)
  · intro k
    exact ((unitUniform_vertexFigure_facet_correspondence (n := 2) hP hvP).1
      (D.facet (T.facetOrder k)) (D.facet_incidence _).1 ((D.facet_incidence _).2.1 hv.1)).1
  · intro i j he
    obtain ⟨t, _, ht⟩ := unitUniform5_single_fan_edge_cover
      classification3D classification4D N S hLIB hS1 hB2 hP hG hn hvP hu D he
    have hleft := ht (left_mem_segment ℝ (T.points i) (T.points j))
    have hright := ht (right_mem_segment ℝ (T.points i) (T.points j))
    rcases (finRotate_four_orbit T.length_four T.anti).2.2 t with ht | ht | ht | ht
    · exact ⟨0, by simpa [TypeIIIActualFanData.figureFacet, TypeIIIActualFanData.facetOrder, ht] using hleft,
        by simpa [TypeIIIActualFanData.figureFacet, TypeIIIActualFanData.facetOrder, ht] using hright⟩
    · exact ⟨1, by simpa [TypeIIIActualFanData.figureFacet, TypeIIIActualFanData.facetOrder, ht] using hleft,
        by simpa [TypeIIIActualFanData.figureFacet, TypeIIIActualFanData.facetOrder, ht] using hright⟩
    · exact ⟨2, by simpa [TypeIIIActualFanData.figureFacet, TypeIIIActualFanData.facetOrder, ht] using hleft,
        by simpa [TypeIIIActualFanData.figureFacet, TypeIIIActualFanData.facetOrder, ht] using hright⟩
    · exact ⟨3, by simpa [TypeIIIActualFanData.figureFacet, TypeIIIActualFanData.facetOrder, ht] using hleft,
        by simpa [TypeIIIActualFanData.figureFacet, TypeIIIActualFanData.facetOrder, ht] using hright⟩

end ActualPolygonCycle
end Uniform5.Composition
