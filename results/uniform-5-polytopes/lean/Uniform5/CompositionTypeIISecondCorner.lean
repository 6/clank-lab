import Uniform5.CompositionPairedTypeIIImpossible

/-! The second trapezoid corner is forced into any actual partner fan
by the same genuine degree-four incidence argument as the first corner. -/
noncomputable section
namespace Uniform5.Composition.TypeIIActualFanData
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIIActualFanData D v n)

theorem first_figure_y_neighbors (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) (w : Space 5) :
    Edge (T.figureFacet hP T.anti) T.base.y w ↔
      w = T.base.b ∨ w = T.base.x ∨ w = T.lateral (finRotate D.length T.anti) := by
  rw [T.figureFacet_intrinsic hP hv]
  have hh := (T.first.figure_neighbors (D.facet_unitUniform hP T.anti)
    (D.cell_facet hP hG T.anti) (by omega : 3 ≤ n)).2.2.2.1 w
  rwa [T.first_base, T.first_apex] at hh

theorem last_figure_y_neighbors (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) (w : Space 5) :
    Edge (T.figureFacet hP ((finRotate D.length).symm T.anti)) T.base.y w ↔
      w = T.base.b ∨ w = T.base.x ∨ w = T.lateral ((finRotate D.length).symm T.anti) := by
  rw [T.figureFacet_intrinsic hP hv]
  have hk : (finRotate D.length).symm T.anti ∉ D.slotsAwayFrom T.anti := by
    rw [D.slotsAwayFrom_mem]
    exact fun hh => hh.2 ((finRotate D.length).apply_symm_apply T.anti)
  have hh := (T.last.figure_neighbors (D.facet_unitUniform hP _)
    (D.cell_facet_of_not_away hP hG T.anti _ hk) (by omega : 3 ≤ n)).2.2.2.1 w
  rwa [T.last_base, T.last_apex] at hh

theorem fan_y_neighbors (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) (w : Space 5) :
    (∃ j : Fin D.length, Edge (T.figureFacet hP j) T.base.y w) ↔
      w = T.base.b ∨ w = T.base.x ∨
      w = T.lateral (finRotate D.length T.anti) ∨
      w = T.lateral ((finRotate D.length).symm T.anti) := by
  have hp := T.points_injective hG (by omega : 3 ≤ n)
  have hxa : T.base.y ≠ T.base.b := fun hh => by
    have h := hp (show T.points 3 = T.points 1 from hh)
    exact (by decide : (3 : Fin 6) ≠ 1) h
  have hxb : T.base.y ≠ T.base.a := fun hh => by
    have h := hp (show T.points 3 = T.points 0 from hh)
    exact (by decide : (3 : Fin 6) ≠ 0) h
  have hxz : T.base.y ≠ T.lateral (finRotate D.length T.anti) := fun hh => by
    have h := hp (show T.points 3 = T.points 4 from hh)
    exact (by decide : (3 : Fin 6) ≠ 4) h
  have hxw : T.base.y ≠ T.lateral ((finRotate D.length).symm T.anti) := fun hh => by
    have h := hp (show T.points 3 = T.points 5 from hh)
    exact (by decide : (3 : Fin 6) ≠ 5) h
  constructor
  · rintro ⟨j, he⟩
    rcases (finRotate_three_orbit T.length_three T.anti).2.2 j with rfl | rfl | hh
    · have h := (T.first_figure_y_neighbors hP hG hn hv w).mp he; tauto
    · have h := (T.last_figure_y_neighbors hP hG hn hv w).mp he; tauto
    · rw [← T.opposite_eq] at hh
      subst j
      have h := ((T.opposite_figure_edges hP hG hn hv T.base.y w).mp he).1
      tauto
  · rintro (h | h | h | h)
    · exact ⟨T.anti, (T.first_figure_y_neighbors hP hG hn hv w).mpr (Or.inl h)⟩
    · exact ⟨T.anti, (T.first_figure_y_neighbors hP hG hn hv w).mpr (Or.inr (Or.inl h))⟩
    · exact ⟨T.anti, (T.first_figure_y_neighbors hP hG hn hv w).mpr (Or.inr (Or.inr h))⟩
    · exact ⟨_, (T.last_figure_y_neighbors hP hG hn hv w).mpr (Or.inr (Or.inr h))⟩

theorem outside_partner_y_neighbors
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} (A : ActualPolygonCycle P H)
    (hcover : TwoLargeFacesCoverAt P v G H)
    (hx : T.base.y ∉ actualPolygonFanVertices hP A v) (w : Space 5) :
    Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) T.base.y w ↔
      w = T.base.b ∨ w = T.base.x ∨
      w = T.lateral (finRotate D.length T.anti) ∨
      w = T.lateral ((finRotate D.length).symm T.anti) := by
  rw [← T.fan_y_neighbors hP hG hn hvG w]
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
        hF.1 (hs (left_mem_segment ℝ T.base.y w))
          (hs (right_mem_segment ℝ T.base.y w))).mp he
      exact ⟨i, heF⟩
    · apply False.elim
      apply hx
      refine ⟨i, ?_⟩
      rw [face_extremePoints_eq hF.1]
      exact ⟨hs (left_mem_segment ℝ T.base.y w), he.1⟩
  · rintro ⟨i, he⟩
    have hvK : v ∈ (D.facet i).extremePoints ℝ := by
      rw [face_extremePoints_eq (D.facet_incidence i).1.1]
      exact ⟨(D.facet_incidence i).2.1 hvG.1,
        hG.1.2.extremePoints_subset_extremePoints hvG⟩
    have hp := unitUniform5_facet_figure_placement hP (D.facet_incidence i).1 hvK
    exact (edge_face_iff hp.1 hp.2.2.1.1 he.1.1 he.2.1.1).mpr he

theorem base_y_mem_partner
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} {m : ℕ}
    (hH : PolygonFace P H m) (A : ActualPolygonCycle P H)
    (hcover : TwoLargeFacesCoverAt P v G H)
    (hcH : Edge H v (T.lateral (finRotate D.length T.anti)))
    (hdH : Edge H v (T.lateral ((finRotate D.length).symm T.anti))) :
    T.base.y ∈ actualPolygonFanVertices hP A v := by
  let e : Fin 5 ↪ Fin 6 := ⟨![1, 2, 4, 5, 3], by decide⟩
  let p : Fin 5 ↪ Space 5 :=
    ⟨fun i => T.points (e i), (T.points_injective hG (by omega)).comp e.injective⟩
  have hp (i : Fin 5) : p i ∈ (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ := by
    apply TypeIFanChart.fan_vertex_extreme hP hG hvG
    rw [T.mem_fan_vertices hP hG hn hvG]
    fin_cases i <;> simp [p, e, points]
  have hcd : T.lateral (finRotate D.length T.anti) ≠
      T.lateral ((finRotate D.length).symm T.anti) := fun hh => by
    have hh' := T.points_injective hG (by omega) (show T.points 4 = T.points 5 from hh)
    exact (by decide : (4 : Fin 6) ≠ 5) hh'
  have hvK : v ∈ (D.facet T.anti).extremePoints ℝ := by
    rw [face_extremePoints_eq (D.facet_incidence T.anti).1.1]
    exact ⟨(D.facet_incidence T.anti).2.1 hvG.1,
      hG.1.2.extremePoints_subset_extremePoints hvG⟩
  have hpK := unitUniform5_facet_figure_placement hP (D.facet_incidence T.anti).1 hvK
  apply finitePolytope_paired_k3_vertex_in_partner hpK.1 hpK.2.1 p hp
    (actualPolygonFanVertices hP A v)
  · intro F hF hc hd x hx
    obtain ⟨i, hi⟩ := unitUniform5_figure_facet_in_polygon_fan hP hH A hcH hdH
      hcd hF hc hd
    exact ⟨i, hi ▸ hx⟩
  · intro hx w
    exact T.outside_partner_y_neighbors classification3D classification4D N S
      hLIB hS1 hB2 hP hG hn hvG A hcover hx w

end Uniform5.Composition.TypeIIActualFanData
