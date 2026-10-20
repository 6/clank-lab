import Uniform5.CompositionTypeIIIFanLabels
import Uniform5.CompositionPyramidFullGraph
import Uniform5.CompositionFourNeighborFigureEdges
import Uniform5.CompositionSevenVertexFan

/-! Actual Type III facet edge graphs, labeled by the seven distinct
vertices constructed from the actual cycle. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem pyramid_label_edges (z : Fin 7) (hz : z = 4 ∨ z = 5) (i j : Fin 7) :
    ((i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = z)) ∨
      (i = 1 ∧ (j = 0 ∨ j = 3 ∨ j = z)) ∨
      (i = 2 ∧ (j = 0 ∨ j = 3 ∨ j = z)) ∨
      (i = 3 ∧ (j = 1 ∨ j = 2 ∨ j = z)) ∨
      (i = z ∧ (j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3))) ↔
      j ∈ CaseB.s1iiiPyramidNeighbours z i := by
  rcases hz with rfl | rfl <;> revert i j <;> decide

theorem tetrahedron_label_edges (V : Finset (Fin 7)) (i j : Fin 7) :
    j ∈ CaseB.tetrahedronNeighbours V i ↔ i ∈ V ∧ j ∈ V ∧ i ≠ j := by
  by_cases hi : i ∈ V <;> simp [CaseB.tetrahedronNeighbours, hi, ne_comm, and_comm]

namespace TypeIIIActualFanData
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
  (T : TypeIIIActualFanData D v n)

noncomputable def facetOrder : Fin 4 → Fin D.length :=
  ![T.anti, (finRotate D.length).symm T.anti,
    finRotate D.length T.anti, finRotate D.length (finRotate D.length T.anti)]

noncomputable def figureFacet (hP : UnitUniform 5 P) (k : Fin 4) : Set (Space 5) :=
  D.facet (T.facetOrder k) ∩ vertexFigure P v
    (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))

theorem figureFacet_intrinsic (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hv : v ∈ G.extremePoints ℝ) (k : Fin 4) :
    T.figureFacet hP k = vertexFigure (D.facet (T.facetOrder k)) v
      (vertexCentroid (vertices (D.facet (T.facetOrder k))
        (uniform_finitePolytope (D.facet_unitUniform hP (T.facetOrder k)).1))) := by
  exact uniform_vertexFigure_face_inter hP.1 (D.facet_incidence _).1.1
    (D.facet_incidence _).1.2.1 ((D.facet_incidence _).2.1 hv.1)

theorem figureFacet_edges (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) :
    ∀ k i j, Edge (T.figureFacet hP k) (T.points i) (T.points j) ↔
      j ∈ CaseB.s1iiiFacetNeighbours k i := by
  have hp := T.points_injective hG (by omega)
  have heq (i j : Fin 7) : T.points i = T.points j ↔ i = j := hp.eq_iff
  let r := finRotate D.length
  let a := T.anti
  have hra := (finRotate_ne_and_twice_ne D.length_ge a).1
  obtain ⟨hrra, hrrra, _⟩ := finRotate_four_orbit T.length_four a
  have hka := D.predecessor_ne a
  have hlast : r.symm a ∉ D.slotsAwayFrom a := by
    rw [D.slotsAwayFrom_mem]
    exact fun h => h.2 (r.apply_symm_apply a)
  have hmid₁ : r a ∈ D.slotsAwayFrom a := (D.slotsAwayFrom_mem a _).mpr ⟨hra, hrra⟩
  have hmid₂ : r (r a) ∈ D.slotsAwayFrom a := by
    apply (D.slotsAwayFrom_mem a _).mpr
    exact ⟨hrra, by change r (r (r a)) ≠ a; rw [hrrra]; exact hka⟩
  intro k i j
  rw [T.figureFacet_intrinsic hP hG hv k]
  fin_cases k
  all_goals simp only [facetOrder, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · have hf := T.first.figure_edges (D.facet_unitUniform hP a) (D.cell_facet hP hG a)
      (by omega : 3 ≤ n)
    rw [hf, T.first_base, T.first_apex]
    change ((T.points i = T.points 0 ∧ (T.points j = T.points 1 ∨ T.points j = T.points 2 ∨ T.points j = T.points 4)) ∨
      (T.points i = T.points 1 ∧ (T.points j = T.points 0 ∨ T.points j = T.points 3 ∨ T.points j = T.points 4)) ∨
      (T.points i = T.points 2 ∧ (T.points j = T.points 0 ∨ T.points j = T.points 3 ∨ T.points j = T.points 4)) ∨
      (T.points i = T.points 3 ∧ (T.points j = T.points 1 ∨ T.points j = T.points 2 ∨ T.points j = T.points 4)) ∨
      (T.points i = T.points 4 ∧ (T.points j = T.points 0 ∨ T.points j = T.points 1 ∨ T.points j = T.points 2 ∨ T.points j = T.points 3))) ↔ _
    simp only [heq]
    exact pyramid_label_edges 4 (Or.inl rfl) i j
  · have hf := T.last.figure_edges (D.facet_unitUniform hP (r.symm a))
      (D.cell_facet_of_not_away hP hG a (r.symm a) hlast) (by omega : 3 ≤ n)
    rw [hf, T.last_base, T.last_apex]
    change ((T.points i = T.points 0 ∧ (T.points j = T.points 1 ∨ T.points j = T.points 2 ∨ T.points j = T.points 5)) ∨
      (T.points i = T.points 1 ∧ (T.points j = T.points 0 ∨ T.points j = T.points 3 ∨ T.points j = T.points 5)) ∨
      (T.points i = T.points 2 ∧ (T.points j = T.points 0 ∨ T.points j = T.points 3 ∨ T.points j = T.points 5)) ∨
      (T.points i = T.points 3 ∧ (T.points j = T.points 1 ∨ T.points j = T.points 2 ∨ T.points j = T.points 5)) ∨
      (T.points i = T.points 5 ∧ (T.points j = T.points 0 ∨ T.points j = T.points 1 ∨ T.points j = T.points 2 ∨ T.points j = T.points 3))) ↔ _
    simp only [heq]
    exact pyramid_label_edges 5 (Or.inr rfl) i j
  · have hf := unitUniform4_four_neighbor_figure_edges (D.facet_unitUniform hP (r a))
      (T.duoprism_slot_neighbors hP hG hn hv (r a) hmid₁)
    rw [hf]
    change ((T.points i = T.points 0 ∨ T.points i = T.points 1 ∨ T.points i = T.points 4 ∨ T.points i = T.points 6) ∧
      (T.points j = T.points 0 ∨ T.points j = T.points 1 ∨ T.points j = T.points 4 ∨ T.points j = T.points 6) ∧
      T.points i ≠ T.points j) ↔ _
    simp only [ne_eq, heq]
    simp [CaseB.s1iiiFacetNeighbours, tetrahedron_label_edges]
  · have hN := T.duoprism_slot_neighbors hP hG hn hv (r (r a)) hmid₂
    rw [hrrra] at hN
    have hf := unitUniform4_four_neighbor_figure_edges (D.facet_unitUniform hP (r (r a))) hN
    rw [hf]
    change ((T.points i = T.points 0 ∨ T.points i = T.points 1 ∨ T.points i = T.points 6 ∨ T.points i = T.points 5) ∧
      (T.points j = T.points 0 ∨ T.points j = T.points 1 ∨ T.points j = T.points 6 ∨ T.points j = T.points 5) ∧
      T.points i ≠ T.points j) ↔ _
    simp only [ne_eq, heq]
    simp [CaseB.s1iiiFacetNeighbours, tetrahedron_label_edges, or_comm, or_left_comm]

end TypeIIIActualFanData
end Uniform5.Composition
