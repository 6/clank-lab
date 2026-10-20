import Uniform5.CompositionTypeIFanChart
import Uniform5.CompositionChartEdges

/-! Complete actual tetrahedral edge lists for each coherently labelled
Type I fan facet. -/
noncomputable section
namespace Uniform5.Composition.TypeIFanChart
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

theorem facet_figure_vertices (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) (i : Fin D.length) :
    (D.facet i ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ =
    {T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} := by
  have hK := (D.facet_incidence i).1
  have hKU := D.facet_unitUniform hP i
  have hvK : v ∈ (D.facet i).extremePoints ℝ := by
    rw [face_extremePoints_eq hK.1]
    exact ⟨(D.facet_incidence i).2.1 hvG.1, hG.1.2.extremePoints_subset_extremePoints hvG⟩
  rw [uniform_vertexFigure_face_inter hP.1 hK.1 hK.2.1 ((D.facet_incidence i).2.1 hvG.1)]
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hKU.1
  rw [finitePolytope_unit_vertexFigure_extremePoints (uniform_finitePolytope hKU.1) hvK _
    (intrinsicRadius (D.facet i)) hs hKU.2]
  ext w
  exact T.facet_neighbors i w

/-- An edge in a fan facet is exactly an unordered distinct pair from
its four literal chart points. -/
theorem facet_figure_edge_iff (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) (i : Fin D.length) (x y : Space 5) :
    Edge (D.facet i ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y ↔
    x ∈ ({T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} : Set (Space 5)) ∧
    y ∈ ({T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} : Set (Space 5)) ∧ x ≠ y := by
  have hK := (D.facet_incidence i).1
  have hvK : v ∈ (D.facet i).extremePoints ℝ := by
    rw [face_extremePoints_eq hK.1]
    exact ⟨(D.facet_incidence i).2.1 hvG.1, hG.1.2.extremePoints_subset_extremePoints hvG⟩
  have hp := unitUniform5_facet_figure_placement hP hK hvK
  have hfinite := finitePolytope_face hp.1 hp.2.2.1.1 hp.2.2.1.2.1
  have hv := T.facet_figure_vertices hP hG hvG i
  constructor
  · intro he
    exact ⟨hv ▸ he.1, hv ▸ he.2.1, he.2.2.1⟩
  · rintro ⟨hx, hy, hne⟩
    exact (tetrahedron_complete_graph hfinite hp.2.2.2.1 hv (hv.symm ▸ hx) (hv.symm ▸ hy)).mpr hne

/-- Every tetrahedron edge is an actual edge of the parent vertex figure. -/
theorem parent_figure_edge (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) (i : Fin D.length) {x y : Space 5}
    (hx : x ∈ ({T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} : Set (Space 5)))
    (hy : y ∈ ({T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} : Set (Space 5)))
    (hne : x ≠ y) : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y := by
  have hK := (D.facet_incidence i).1
  have hvK : v ∈ (D.facet i).extremePoints ℝ := by
    rw [face_extremePoints_eq hK.1]
    exact ⟨(D.facet_incidence i).2.1 hvG.1, hG.1.2.extremePoints_subset_extremePoints hvG⟩
  have hp := unitUniform5_facet_figure_placement hP hK hvK
  have he := (T.facet_figure_edge_iff hP hG hvG i x y).mpr ⟨hx, hy, hne⟩
  exact (edge_face_iff hp.1 hp.2.2.1.1 he.1.1 he.2.1.1).mpr he

end Uniform5.Composition.TypeIFanChart
