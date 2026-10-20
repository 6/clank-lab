import Uniform5.CompositionTypeIICoherentEdges
import Uniform5.CompositionTypeIFanVertexSet

/-! Actual complete neighbors of a Type II base corner outside the
partner fan, derived from two-fan edge coverage. -/
noncomputable section
namespace Uniform5.Composition.TypeIIActualFanData
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIIActualFanData D v n)

theorem mem_fan_vertices (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ) (w : Space 5) :
    w ∈ actualPolygonFanVertices hP D v ↔
      w = T.base.a ∨ w = T.base.b ∨ w = T.base.x ∨ w = T.base.y ∨
      w = T.lateral (finRotate D.length T.anti) ∨
      w = T.lateral ((finRotate D.length).symm T.anti) :=
  T.fan_vertex_iff hP hG hn hvG w

theorem outside_partner_x_neighbors
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} (A : ActualPolygonCycle P H)
    (hcover : TwoLargeFacesCoverAt P v G H)
    (hx : T.base.x ∉ actualPolygonFanVertices hP A v) (w : Space 5) :
    Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) T.base.x w ↔
      w = T.base.a ∨ w = T.base.y ∨
      w = T.lateral (finRotate D.length T.anti) ∨
      w = T.lateral ((finRotate D.length).symm T.anti) := by
  rw [← T.fan_x_neighbors hP hG hn hvG w]
  constructor
  · intro he
    rcases unitUniform5_two_fan_edge_cover classification3D classification4D N S
      hLIB hS1 hB2 hP hG hn (hG.1.2.extremePoints_subset_extremePoints hvG)
      hcover D A he with ⟨i, hF, hs⟩ | ⟨i, hF, hs⟩
    · have heF := (edge_face_iff
        (unitUniform5_facet_figure_placement hP (D.facet_incidence i).1
          (by rw [face_extremePoints_eq (D.facet_incidence i).1.1]
              exact ⟨(D.facet_incidence i).2.1 hvG.1,
                hG.1.2.extremePoints_subset_extremePoints hvG⟩)).1
        hF.1 (hs (left_mem_segment ℝ T.base.x w))
          (hs (right_mem_segment ℝ T.base.x w))).mp he
      exact ⟨i, heF⟩
    · apply False.elim
      apply hx
      refine ⟨i, ?_⟩
      rw [face_extremePoints_eq hF.1]
      exact ⟨hs (left_mem_segment ℝ T.base.x w), he.1⟩
  · rintro ⟨i, he⟩
    have hvK : v ∈ (D.facet i).extremePoints ℝ := by
      rw [face_extremePoints_eq (D.facet_incidence i).1.1]
      exact ⟨(D.facet_incidence i).2.1 hvG.1,
        hG.1.2.extremePoints_subset_extremePoints hvG⟩
    have hp := unitUniform5_facet_figure_placement hP (D.facet_incidence i).1 hvK
    exact (edge_face_iff hp.1 hp.2.2.1.1 he.1.1 he.2.1.1).mpr he

end Uniform5.Composition.TypeIIActualFanData
