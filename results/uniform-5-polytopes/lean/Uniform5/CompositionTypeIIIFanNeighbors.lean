import Uniform5.CompositionTypeIIIActualFanData

/-! The coherent type-III fan exhausts actual neighbors facet by facet. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem finRotate_four_orbit {m : ℕ} (hm : m = 4) (a : Fin m) :
    (finRotate m (finRotate m a) ≠ a) ∧
    (finRotate m (finRotate m (finRotate m a)) = (finRotate m).symm a) ∧
    (∀ t : Fin m, t = a ∨ t = (finRotate m).symm a ∨
      t = finRotate m a ∨ t = finRotate m (finRotate m a)) := by
  subst m
  revert a
  decide

namespace TypeIIIActualFanData
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
  (T : TypeIIIActualFanData D v n)

theorem duoprism_slot_neighbors (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) (j : Fin D.length)
    (hj : j ∈ D.slotsAwayFrom T.anti) :
    ∀ w, Edge (D.facet j) v w ↔
      w = T.base.a ∨ w = T.base.b ∨ w = T.lateral j ∨
        w = T.lateral (finRotate D.length j) := by
  obtain ⟨hja, hrja⟩ := (D.slotsAwayFrom_mem T.anti j).mp hj
  obtain ⟨q, hq, hmodel⟩ := T.duoprism j hj
  have hGK : PolygonFace (D.facet j) G n :=
    ⟨face_restrict hG.1 (D.facet_incidence j).1.1.2.1 (D.facet_incidence j).2.1, hG.2⟩
  obtain ⟨B⟩ := unitUniform4_duoprism_neighbor_chart_parameters (D.facet_unitUniform hP j)
    (by omega) hq hmodel hGK (by omega) hv
  have hvK := hGK.1.2.extremePoints_subset_extremePoints hv
  apply finitePolytope_simpleVertex_two_triangle_neighbors
    (uniform_finitePolytope (D.facet_unitUniform hP j).1)
    (uniform_dimension (D.facet_unitUniform hP j).1) hvK
    (B.neighbour_card (D.facet_unitUniform hP j) hvK)
    (D.cell_facet hP hG j) (D.next_cell_facet hP hG j) ?_
    (T.lateral_edges j hja) (T.lateral_edges _ hrja)
  intro he
  have hi := D.cell_injective j.isLt (finRotate D.length j).isLt he
  exact (finRotate_ne_and_twice_ne D.length_ge j).1 (Fin.ext hi).symm

theorem first_neighbors :
    ∀ w, Edge (D.facet T.anti) v w ↔
      w = T.base.a ∨ w = T.base.b ∨ w = T.base.x ∨ w = T.base.y ∨
        w = T.lateral (finRotate D.length T.anti) := by
  intro w
  have hh := T.first.neighbors w
  rwa [T.first_base, T.first_apex] at hh

theorem last_neighbors :
    ∀ w, Edge (D.facet ((finRotate D.length).symm T.anti)) v w ↔
      w = T.base.a ∨ w = T.base.b ∨ w = T.base.x ∨ w = T.base.y ∨
        w = T.lateral ((finRotate D.length).symm T.anti) := by
  intro w
  have hh := T.last.neighbors w
  rwa [T.last_base, T.last_apex] at hh

/-- The actual single-fan cover gives the complete seven-point neighbor
list, once the coherent fan has been constructed from the actual cycle. -/
theorem parent_neighbors
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hv : v ∈ G.extremePoints ℝ) (hu : UniqueLargeFaceAt P v G) :
    ∀ w, Edge P v w ↔
      w = T.base.a ∨ w = T.base.b ∨ w = T.base.x ∨ w = T.base.y ∨
      w = T.lateral (finRotate D.length T.anti) ∨
      w = T.lateral ((finRotate D.length).symm T.anti) ∨
      w = T.lateral (finRotate D.length (finRotate D.length T.anti)) := by
  let r := finRotate D.length
  let a := T.anti
  obtain ⟨hrra, hrrra, hcover⟩ := finRotate_four_orbit T.length_four a
  have hra : r a ≠ a := (finRotate_ne_and_twice_ne D.length_ge a).1
  have hk : r.symm a ≠ a := D.predecessor_ne a
  have hmid₁ : r a ∈ D.slotsAwayFrom a := (D.slotsAwayFrom_mem a _).mpr ⟨hra, hrra⟩
  have hmid₂ : r (r a) ∈ D.slotsAwayFrom a := by
    apply (D.slotsAwayFrom_mem a _).mpr
    exact ⟨hrra, by change r (r (r a)) ≠ a; rw [hrrra]; exact hk⟩
  have lift (j : Fin D.length) (w : Space 5) (he : Edge (D.facet j) v w) : Edge P v w :=
    (edge_face_iff (uniform_finitePolytope hP.1) (D.facet_incidence j).1.1 he.1.1 he.2.1.1).mpr he
  intro w
  constructor
  · intro he
    obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
    have hwV : w ∈ (vertexFigure P v
        (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ := by
      rw [finitePolytope_unit_vertexFigure_extremePoints
        (uniform_finitePolytope hP.1) he.1 _ (intrinsicRadius P) hs hP.2]
      exact he
    obtain ⟨j, hj⟩ := unitUniform5_single_fan_vertex_cover
      classification3D classification4D N S hLIB hS1 hB2 hP hG hn he.1 hu D hwV
    have hev := (edge_face_iff (uniform_finitePolytope hP.1) (D.facet_incidence j).1.1
      ((D.facet_incidence j).2.1 hv.1) hj.1.1).mp he
    rcases hcover j with h | h | h | h
    · subst j
      have hh := (T.first_neighbors w).mp hev
      tauto
    · subst j
      have hh := (T.last_neighbors w).mp hev
      tauto
    · subst j
      have hh := (T.duoprism_slot_neighbors hP hG hn hv (r a) hmid₁ w).mp hev
      tauto
    · subst j
      have hh := (T.duoprism_slot_neighbors hP hG hn hv (r (r a)) hmid₂ w).mp hev
      rw [hrrra] at hh
      tauto
  · intro hh
    rcases hh with h | h | h | h | h | h | h
    · exact lift a w ((T.first_neighbors w).mpr (Or.inl h))
    · exact lift a w ((T.first_neighbors w).mpr (Or.inr (Or.inl h)))
    · exact lift a w ((T.first_neighbors w).mpr (Or.inr (Or.inr (Or.inl h))))
    · exact lift a w ((T.first_neighbors w).mpr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact lift a w ((T.first_neighbors w).mpr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    · exact lift (r.symm a) w ((T.last_neighbors w).mpr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    · exact lift (r a) w ((T.duoprism_slot_neighbors hP hG hn hv (r a) hmid₁ w).mpr
        (Or.inr (Or.inr (Or.inr h))))

end TypeIIIActualFanData
end Uniform5.Composition
