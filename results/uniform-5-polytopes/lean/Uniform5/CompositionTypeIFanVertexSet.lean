import Uniform5.CompositionTypeIFanMetrics
import Uniform5.CompositionTypeIFanEdges
import Uniform5.CompositionTwoFanCover

/-! Actual polygon fan vertex sets and complete neighbor information
outside the second large-polygon fan. -/
noncomputable section
namespace Uniform5.Composition
open Set

noncomputable def actualPolygonFanVertices {P G : Set (Space 5)}
    (hP : UnitUniform 5 P) (D : ActualPolygonCycle P G) (v : Space 5) : Set (Space 5) :=
  {x | ∃ i : Fin D.length, x ∈ (D.facet i ∩ vertexFigure P v
    (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ}

namespace TypeIFanChart
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

theorem mem_fan_vertices (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) (x : Space 5) :
    x ∈ actualPolygonFanVertices hP D v ↔ x = T.a ∨ x = T.b ∨ ∃ i, x = T.lateral i := by
  constructor
  · rintro ⟨i, hx⟩
    rw [T.facet_figure_vertices hP hG hvG i] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨i, rfl⟩)
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
  · rintro (rfl | rfl | ⟨i, rfl⟩)
    · refine ⟨⟨0, by have := D.length_ge; omega⟩, ?_⟩
      rw [T.facet_figure_vertices hP hG hvG]
      simp
    · refine ⟨⟨0, by have := D.length_ge; omega⟩, ?_⟩
      rw [T.facet_figure_vertices hP hG hvG]
      simp
    · refine ⟨i, ?_⟩
      rw [T.facet_figure_vertices hP hG hvG]
      simp

theorem fan_vertex_extreme (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) {x : Space 5}
    (hx : x ∈ actualPolygonFanVertices hP D v) :
    x ∈ (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ := by
  obtain ⟨i, hi⟩ := hx
  have hK := (D.facet_incidence i).1
  have hvK : v ∈ (D.facet i).extremePoints ℝ := by
    rw [face_extremePoints_eq hK.1]
    exact ⟨(D.facet_incidence i).2.1 hvG.1, hG.1.2.extremePoints_subset_extremePoints hvG⟩
  exact (unitUniform5_facet_figure_placement hP hK hvK).2.2.1.1.2.extremePoints_subset_extremePoints hi

theorem fan_metric (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hvG : v ∈ G.extremePoints ℝ)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    {z : Space 5} (hz : z ∈ actualPolygonFanVertices hP D v)
    (hza : z ≠ T.a) (hzb : z ≠ T.b) :
    dist z T.a = Real.sqrt 2 ∧ dist z T.b = Real.sqrt 2 := by
  rcases (T.mem_fan_vertices hP hG hvG z).mp hz with hz | hz | ⟨i, rfl⟩
  · exact (hza hz).elim
  · exact (hzb hz).elim
  · simpa only [dist_comm] using T.cross_dist hP hG hn hn4 hvG i (hq i) (hmodel i)

/-- Outside the other fan, every actual edge comes from a literal
four-point tetrahedron of this coherent fan, and all such pairs are edges. -/
theorem outside_partner_edge_iff
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} (A : ActualPolygonCycle P H)
    (hcover : TwoLargeFacesCoverAt P v G H) {z w : Space 5}
    (hz : z ∉ actualPolygonFanVertices hP A v) :
    Edge (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) z w ↔
    ∃ i : Fin D.length,
      z ∈ ({T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} : Set (Space 5)) ∧
      w ∈ ({T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} : Set (Space 5)) ∧ z ≠ w := by
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
        hF.1 (hs (left_mem_segment ℝ z w)) (hs (right_mem_segment ℝ z w))).mp he
      exact ⟨i, (T.facet_figure_edge_iff hP hG hvG i z w).mp heF⟩
    · apply False.elim
      apply hz
      refine ⟨i, ?_⟩
      rw [face_extremePoints_eq hF.1]
      exact ⟨hs (left_mem_segment ℝ z w), he.1⟩
  · rintro ⟨i, hz, hw, hne⟩
    exact T.parent_figure_edge hP hG hvG i hz hw hne

end TypeIFanChart
end Uniform5.Composition
