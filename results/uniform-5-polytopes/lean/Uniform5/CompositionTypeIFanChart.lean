import Uniform5.CompositionTypeIIFanNeighbors
import Uniform5.CompositionDuoprismCellThirdNeighbor

/-! A coherent actual Type I fan uses one polygon-neighbor pair and one
lateral vertex for each actual prism cell. -/
noncomputable section
namespace Uniform5.Composition
open Set

structure TypeIFanChart {P G : Set (Space 5)} (D : ActualPolygonCycle P G)
    (v : Space 5) (n : ℕ) where
  a : Space 5
  b : Space 5
  lateral : Fin D.length → Space 5
  ab_ne : a ≠ b
  polygon_neighbors : ∀ w, Edge G v w ↔ w = a ∨ w = b
  chord_ab : dist a b = CaseB.chord n
  lateral_mem : ∀ i : Fin D.length, lateral i ∈ D.cell i
  lateral_outside : ∀ i : Fin D.length, lateral i ∉ G
  lateral_ne_a : ∀ i : Fin D.length, lateral i ≠ a
  lateral_ne_b : ∀ i : Fin D.length, lateral i ≠ b
  lateral_injective : Function.Injective lateral
  cell_neighbors : ∀ (i : Fin D.length) w, Edge (D.cell i) v w ↔ w = a ∨ w = b ∨ w = lateral i
  facet_neighbors : ∀ (i : Fin D.length) w, Edge (D.facet i) v w ↔
    w = a ∨ w = b ∨ w = lateral i ∨ w = lateral (finRotate D.length i)

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

theorem typeI_fan_chart {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) {v : Space 5} (hvG : v ∈ G.extremePoints ℝ)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i))) :
    Nonempty (TypeIFanChart D v n) := by
  have hGF (i : Fin D.length) : PolygonFace (D.facet i) G n :=
    ⟨face_restrict hG.1 (D.facet_incidence i).1.1.2.1 (D.facet_incidence i).2.1, hG.2⟩
  have ht (i : Fin D.length) : Nonempty (DuoprismNeighborChart (D.facet i) G v n (q i)) :=
    unitUniform4_duoprism_neighbor_chart_parameters (D.facet_unitUniform hP i)
      hn (hq i) (hmodel i) (hGF i) hn4 hvG
  let i₀ : Fin D.length := ⟨0, by have := D.length_ge; omega⟩
  obtain ⟨T⟩ := ht i₀
  have hz (i : Fin D.length) : ∃ z, z ∈ D.cell i ∧ z ∉ G ∧ z ≠ T.a ∧ z ≠ T.b ∧
      ∀ w, Edge (D.cell i) v w ↔ w = T.a ∨ w = T.b ∨ w = z :=
    unitUniform4_duoprism_cell_third_neighbor (D.facet_unitUniform hP i)
      hn (hq i) hn4 (hmodel i) (hGF i) hvG (D.cell_facet hP hG i)
      (D.cell_contains i) T.polygon_neighbors T.ab_ne
  choose z hzmem hzout hza hzb hzedge using hz
  have hzinj : Function.Injective z := by
    intro i j he
    by_contra hij
    have hcells : D.cell i ≠ D.cell j := fun hh => hij (Fin.ext
      (D.cell_injective i.isLt j.isLt hh))
    exact actual_cell_lateral_points_ne hG.1 (D.cell_face i) (D.cell_face j)
      (polygonFace_nonempty hG) (D.cell_contains i) (D.cell_contains j)
      hG.2.1 (D.cell_dimension i) (D.cell_dimension j) hcells (hzmem i) (hzmem j) (hzout i) he
  refine ⟨⟨T.a, T.b, z, T.ab_ne, T.polygon_neighbors, T.chord_ab,
    hzmem, hzout, hza, hzb, hzinj, hzedge, ?_⟩⟩
  intro i w
  obtain ⟨U⟩ := ht i
  have hvK := (hGF i).1.2.extremePoints_subset_extremePoints hvG
  have hcn : D.cell i ≠ D.cell (finRotate D.length i) := by
    rw [cycle_apply_finRotate (by have := D.length_ge; omega) D.cell D.cell_closed i]
    exact cell_cycle_consecutive_ne D.length_ge D.cell D.cell_closed D.cell_injective i.isLt
  exact finitePolytope_simpleVertex_two_triangle_neighbors
    (uniform_finitePolytope (D.facet_unitUniform hP i).1)
    (uniform_dimension (D.facet_unitUniform hP i).1) hvK
    (U.neighbour_card (D.facet_unitUniform hP i) hvK)
    (D.cell_facet hP hG i) (D.next_cell_facet hP hG i) hcn
    (hzedge i) (hzedge (finRotate D.length i)) w

end ActualPolygonCycle

namespace TypeIFanChart
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

theorem facet_figure (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) (i : Fin D.length) :
    D.facet i ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) =
    convexHull ℝ ({T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} : Set (Space 5)) := by
  have hK := (D.facet_incidence i).1
  have hKU := D.facet_unitUniform hP i
  have hvK : v ∈ (D.facet i).extremePoints ℝ := by
    rw [face_extremePoints_eq hK.1]
    exact ⟨(D.facet_incidence i).2.1 hvG.1, hG.1.2.extremePoints_subset_extremePoints hvG⟩
  rw [uniform_vertexFigure_face_inter hP.1 hK.1 hK.2.1 ((D.facet_incidence i).2.1 hvG.1)]
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hKU.1
  rw [finitePolytope_unit_vertexFigure (uniform_finitePolytope hKU.1) hvK _
    (intrinsicRadius (D.facet i)) hs hKU.2]
  congr 1
  ext w
  exact T.facet_neighbors i w

end TypeIFanChart
end Uniform5.Composition
