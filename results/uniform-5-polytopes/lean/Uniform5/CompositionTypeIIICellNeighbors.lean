import Uniform5.CompositionDuoprismCellThirdNeighbor
import Uniform5.CompositionTypeIIFanNeighbors
import Uniform5.CompositionAntiprismChartEdges

/-! Three distinct actual lateral neighbors in a type-III polygon cycle. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem finRotate_four_cell_incident_tail {m : ℕ} (hm : m = 4)
    (a t : Fin m) (ht : t ≠ a) :
    ∃ j : Fin m, j ≠ a ∧ finRotate m j ≠ a ∧ (j = t ∨ finRotate m j = t) := by
  subst m
  exact (by decide : ∀ a t : Fin 4, t ≠ a →
    ∃ j : Fin 4, j ≠ a ∧ finRotate 4 j ≠ a ∧ (j = t ∨ finRotate 4 j = t)) a t ht

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- Every non-antiprism cell in the actual type-III cycle has one unique
lateral neighbor, distinct from the common two polygon neighbors. -/
theorem typeIII_cell_third_neighbors {n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (hn : 17 ≤ n) {v : Space 5}
    (hv : v ∈ G.extremePoints ℝ) (hlen : D.length = 4)
    (a i j : Fin D.length) (q r : ℕ) (hq : 3 ≤ q) (hr : 3 ≤ r)
    (haway : D.slotsAwayFrom a = {i, j})
    (hqi : Congruent (D.facet i) (duoprismModel n q))
    (hrj : Congruent (D.facet j) (duoprismModel n r))
    (B : AntiprismNeighborChart (D.cell a) G v n) :
    ∀ t : Fin D.length, t ≠ a →
      ∃ z, z ∈ D.cell t ∧ z ∉ G ∧ z ≠ B.a ∧ z ≠ B.b ∧
        ∀ w, Edge (D.cell t) v w ↔ w = B.a ∨ w = B.b ∨ w = z := by
  have hab : B.a ≠ B.b := by
    intro he
    have hh := B.chord_ab
    rw [he, dist_self] at hh
    have hc := CaseB.case_chord_pos (q := n) (by exact_mod_cast (show 3 ≤ n by omega))
    linarith
  intro t ht
  obtain ⟨u, hua, hrua, hut⟩ := finRotate_four_cell_incident_tail hlen a t ht
  have huaway : u ∈ D.slotsAwayFrom a := (D.slotsAwayFrom_mem a u).mpr ⟨hua, hrua⟩
  have hC : Facet (D.facet u) (D.cell t) := by
    rcases hut with he | he
    · rw [← he]; exact D.cell_facet hP hG u
    · rw [← he]; exact D.next_cell_facet hP hG u
  have hGK : PolygonFace (D.facet u) G n :=
    ⟨face_restrict hG.1 (D.facet_incidence u).1.1.2.1 (D.facet_incidence u).2.1, hG.2⟩
  have huij : u = i ∨ u = j := by simpa [haway] using huaway
  rcases huij with rfl | rfl
  · exact unitUniform4_duoprism_cell_third_neighbor (D.facet_unitUniform hP u)
      (by omega) hq (by omega) hqi hGK hv hC (D.cell_contains t) B.polygon_neighbors hab
  · exact unitUniform4_duoprism_cell_third_neighbor (D.facet_unitUniform hP u)
      (by omega) hr (by omega) hrj hGK hv hC (D.cell_contains t) B.polygon_neighbors hab

/-- Lateral chart points of the three actual prism cells are pairwise
distinct, derived from incidence and the cycle's actual cell injectivity. -/
theorem cell_lateral_points_injective {n : ℕ} (hG : PolygonFace P G n)
    {s t : Fin D.length} (hst : s ≠ t) {z w : Space 5}
    (hz : z ∈ D.cell s) (hw : w ∈ D.cell t) (hzG : z ∉ G) : z ≠ w := by
  apply actual_cell_lateral_points_ne hG.1 (D.cell_face s) (D.cell_face t)
    (polygonFace_nonempty hG) (D.cell_contains s) (D.cell_contains t)
    hG.2.1 (D.cell_dimension s) (D.cell_dimension t) ?_ hz hw hzG
  intro he
  have hi := D.cell_injective s.isLt t.isLt he
  exact hst (Fin.ext hi)

end ActualPolygonCycle
end Uniform5.Composition
