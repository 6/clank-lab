import Uniform5.CompositionTypeIIActualFanData

/-! The coherent type-II fan exhausts actual neighbors facet by facet. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem finRotate_three_orbit {m : ℕ} (hm : m = 3) (a : Fin m) :
    finRotate m a ≠ (finRotate m).symm a ∧
    finRotate m (finRotate m a) = (finRotate m).symm a ∧
    (∀ t : Fin m, t = a ∨ t = (finRotate m).symm a ∨ t = finRotate m a) := by
  subst m
  revert a
  decide

namespace TypeIIActualFanData
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
  (T : TypeIIActualFanData D v n)

theorem duoprism_slot_neighbors (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) (j : Fin D.length)
    (hj : j ∈ D.slotsAwayFrom T.anti) :
    ∀ w, Edge (D.facet j) v w ↔
      w = T.base.a ∨ w = T.base.b ∨ w = T.lateral j ∨
        w = T.lateral (finRotate D.length j) := by
  obtain ⟨hja, hrja⟩ := (D.slotsAwayFrom_mem T.anti j).mp hj
  have hjop : j = T.opposite := by simpa [T.away] using hj
  obtain ⟨q, hq, hmodel⟩ := T.duoprism
  rw [← hjop] at hmodel
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

theorem opposite_eq : T.opposite = finRotate D.length T.anti := by
  have hi : T.opposite ∈ D.slotsAwayFrom T.anti := by rw [T.away]; simp
  obtain ⟨hia, hria⟩ := (D.slotsAwayFrom_mem T.anti _).mp hi
  exact (finRotate_three_other T.length_three T.anti T.opposite hia hria).1.symm

theorem fan_neighbors (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) (w : Space 5) :
    (∃ j : Fin D.length, Edge (D.facet j) v w) ↔
      w = T.base.a ∨ w = T.base.b ∨ w = T.base.x ∨ w = T.base.y ∨
      w = T.lateral (finRotate D.length T.anti) ∨
      w = T.lateral ((finRotate D.length).symm T.anti) := by
  obtain ⟨_, hrr, hcover⟩ := finRotate_three_orbit T.length_three T.anti
  have hmid : finRotate D.length T.anti ∈ D.slotsAwayFrom T.anti := by
    rw [T.away, ← T.opposite_eq]; simp
  constructor
  · rintro ⟨j, he⟩
    rcases hcover j with rfl | rfl | rfl
    · have hh := (T.first_neighbors w).mp he; tauto
    · have hh := (T.last_neighbors w).mp he; tauto
    · have hh := (T.duoprism_slot_neighbors hP hG hn hv _ hmid w).mp he
      rw [hrr] at hh
      tauto
  · rintro (h | h | h | h | h | h)
    · exact ⟨T.anti, (T.first_neighbors w).mpr (Or.inl h)⟩
    · exact ⟨T.anti, (T.first_neighbors w).mpr (Or.inr (Or.inl h))⟩
    · exact ⟨T.anti, (T.first_neighbors w).mpr (Or.inr (Or.inr (Or.inl h)))⟩
    · exact ⟨T.anti, (T.first_neighbors w).mpr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
    · exact ⟨T.anti, (T.first_neighbors w).mpr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
    · exact ⟨_, (T.last_neighbors w).mpr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩

end TypeIIActualFanData
end Uniform5.Composition
