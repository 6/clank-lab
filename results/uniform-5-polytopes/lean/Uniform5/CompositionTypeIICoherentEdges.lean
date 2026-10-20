import Uniform5.CompositionTypeIICoherentLabels
import Uniform5.CompositionPyramidFullGraph
import Uniform5.CompositionFourNeighborFigureEdges

/-! Exact actual Type II fan vertex and edge relations. -/
noncomputable section
namespace Uniform5.Composition.TypeIIActualFanData
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIIActualFanData D v n)

noncomputable def figureFacet (T : TypeIIActualFanData D v n) (hP : UnitUniform 5 P) (j : Fin D.length) : Set (Space 5) :=
  D.facet j ∩ vertexFigure P v
    (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))

theorem figureFacet_intrinsic (hP : UnitUniform 5 P)
    (hv : v ∈ G.extremePoints ℝ) (j : Fin D.length) :
    T.figureFacet hP j = vertexFigure (D.facet j) v
      (vertexCentroid (vertices (D.facet j)
        (uniform_finitePolytope (D.facet_unitUniform hP j).1))) := by
  exact uniform_vertexFigure_face_inter hP.1 (D.facet_incidence _).1.1
    (D.facet_incidence _).1.2.1 ((D.facet_incidence _).2.1 hv.1)

theorem figureFacet_vertex_iff (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (hv : v ∈ G.extremePoints ℝ)
    (j : Fin D.length) (w : Space 5) :
    w ∈ (T.figureFacet hP j).extremePoints ℝ ↔ Edge (D.facet j) v w := by
  rw [T.figureFacet_intrinsic hP hv j]
  have hvK : v ∈ (D.facet j).extremePoints ℝ := by
    rw [face_extremePoints_eq (D.facet_incidence j).1.1]
    exact ⟨(D.facet_incidence j).2.1 hv.1, hG.1.2.extremePoints_subset_extremePoints hv⟩
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius (D.facet_unitUniform hP j).1
  rw [finitePolytope_unit_vertexFigure_extremePoints
    (uniform_finitePolytope (D.facet_unitUniform hP j).1) hvK _
    (intrinsicRadius (D.facet j)) hs (D.facet_unitUniform hP j).2]
  rfl

theorem fan_vertex_iff (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) (w : Space 5) :
    (∃ j : Fin D.length, w ∈ (T.figureFacet hP j).extremePoints ℝ) ↔
      w = T.base.a ∨ w = T.base.b ∨ w = T.base.x ∨ w = T.base.y ∨
      w = T.lateral (finRotate D.length T.anti) ∨
      w = T.lateral ((finRotate D.length).symm T.anti) := by
  simp_rw [T.figureFacet_vertex_iff hP hG hv]
  exact T.fan_neighbors hP hG hn hv w

theorem opposite_figure_edges (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) (u w : Space 5) :
    Edge (T.figureFacet hP T.opposite) u w ↔
      (u = T.base.a ∨ u = T.base.b ∨ u = T.lateral (finRotate D.length T.anti) ∨
        u = T.lateral ((finRotate D.length).symm T.anti)) ∧
      (w = T.base.a ∨ w = T.base.b ∨ w = T.lateral (finRotate D.length T.anti) ∨
        w = T.lateral ((finRotate D.length).symm T.anti)) ∧ u ≠ w := by
  rw [T.figureFacet_intrinsic hP hv]
  have hj : T.opposite ∈ D.slotsAwayFrom T.anti := by rw [T.away]; simp
  have hh := T.duoprism_slot_neighbors hP hG hn hv _ hj
  rw [T.opposite_eq, (finRotate_three_orbit T.length_three T.anti).2.1] at hh
  exact unitUniform4_four_neighbor_figure_edges (D.facet_unitUniform hP T.opposite)
    (by simpa only [T.opposite_eq] using hh) u w

theorem first_figure_x_neighbors (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) (w : Space 5) :
    Edge (T.figureFacet hP T.anti) T.base.x w ↔
      w = T.base.a ∨ w = T.base.y ∨ w = T.lateral (finRotate D.length T.anti) := by
  rw [T.figureFacet_intrinsic hP hv]
  have hh := (T.first.figure_neighbors (D.facet_unitUniform hP T.anti)
    (D.cell_facet hP hG T.anti) (by omega : 3 ≤ n)).2.2.1 w
  rwa [T.first_base, T.first_apex] at hh

theorem last_figure_x_neighbors (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) (w : Space 5) :
    Edge (T.figureFacet hP ((finRotate D.length).symm T.anti)) T.base.x w ↔
      w = T.base.a ∨ w = T.base.y ∨ w = T.lateral ((finRotate D.length).symm T.anti) := by
  rw [T.figureFacet_intrinsic hP hv]
  have hk : (finRotate D.length).symm T.anti ∉ D.slotsAwayFrom T.anti := by
    rw [D.slotsAwayFrom_mem]
    exact fun hh => hh.2 ((finRotate D.length).apply_symm_apply T.anti)
  have hh := (T.last.figure_neighbors (D.facet_unitUniform hP _)
    (D.cell_facet_of_not_away hP hG T.anti _ hk) (by omega : 3 ≤ n)).2.2.1 w
  rwa [T.last_base, T.last_apex] at hh

theorem fan_x_neighbors (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) (w : Space 5) :
    (∃ j : Fin D.length, Edge (T.figureFacet hP j) T.base.x w) ↔
      w = T.base.a ∨ w = T.base.y ∨
      w = T.lateral (finRotate D.length T.anti) ∨
      w = T.lateral ((finRotate D.length).symm T.anti) := by
  have hp := T.points_injective hG (by omega : 3 ≤ n)
  have hxa : T.base.x ≠ T.base.a := fun hh => by
    have h := hp (show T.points 2 = T.points 0 from hh)
    exact (by decide : (2 : Fin 6) ≠ 0) h
  have hxb : T.base.x ≠ T.base.b := fun hh => by
    have h := hp (show T.points 2 = T.points 1 from hh)
    exact (by decide : (2 : Fin 6) ≠ 1) h
  have hxz : T.base.x ≠ T.lateral (finRotate D.length T.anti) := fun hh => by
    have h := hp (show T.points 2 = T.points 4 from hh)
    exact (by decide : (2 : Fin 6) ≠ 4) h
  have hxw : T.base.x ≠ T.lateral ((finRotate D.length).symm T.anti) := fun hh => by
    have h := hp (show T.points 2 = T.points 5 from hh)
    exact (by decide : (2 : Fin 6) ≠ 5) h
  constructor
  · rintro ⟨j, he⟩
    rcases (finRotate_three_orbit T.length_three T.anti).2.2 j with rfl | rfl | hh
    · have h := (T.first_figure_x_neighbors hP hG hn hv w).mp he; tauto
    · have h := (T.last_figure_x_neighbors hP hG hn hv w).mp he; tauto
    · rw [← T.opposite_eq] at hh
      subst j
      have h := ((T.opposite_figure_edges hP hG hn hv T.base.x w).mp he).1
      exact False.elim (h.elim hxa (fun h => h.elim hxb (fun h => h.elim hxz hxw)))
  · rintro (h | h | h | h)
    · exact ⟨T.anti, (T.first_figure_x_neighbors hP hG hn hv w).mpr (Or.inl h)⟩
    · exact ⟨T.anti, (T.first_figure_x_neighbors hP hG hn hv w).mpr (Or.inr (Or.inl h))⟩
    · exact ⟨T.anti, (T.first_figure_x_neighbors hP hG hn hv w).mpr (Or.inr (Or.inr h))⟩
    · exact ⟨_, (T.last_figure_x_neighbors hP hG hn hv w).mpr (Or.inr (Or.inr h))⟩

end Uniform5.Composition.TypeIIActualFanData
