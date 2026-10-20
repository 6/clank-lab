import Uniform5.CompositionTypeIIPairedNeighbors
import Uniform5.CompositionTypeIIPartnerEndpoints
import Uniform5.CaseBCaseMetrics

/-! A Type II fan vertex outside its duoprism facet is a base corner.
Its antiprism diagonal supplies the mixed-case metric obstruction. -/
noncomputable section
namespace Uniform5.Composition.TypeIIActualFanData
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIIActualFanData D v n)

theorem opposite_figure_vertices (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ) :
    (T.figureFacet hP T.opposite).extremePoints ℝ =
      {T.base.a, T.base.b, T.lateral (finRotate D.length T.anti),
        T.lateral ((finRotate D.length).symm T.anti)} := by
  ext w
  rw [T.figureFacet_vertex_iff hP hG hvG]
  have hi : T.opposite ∈ D.slotsAwayFrom T.anti := by rw [T.away]; simp
  have hh := T.duoprism_slot_neighbors hP hG hn hvG _ hi w
  simpa only [T.opposite_eq, (finRotate_three_orbit T.length_three T.anti).2.1] using hh

theorem fan_outside_opposite (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ) {z : Space 5}
    (hz : z ∈ actualPolygonFanVertices hP D v)
    (hout : z ∉ (T.figureFacet hP T.opposite).extremePoints ℝ) :
    z = T.base.x ∨ z = T.base.y := by
  rw [T.opposite_figure_vertices hP hG hn hvG] at hout
  rcases (T.mem_fan_vertices hP hG hn hvG z).mp hz with h | h | h | h | h | h
  · exact (hout (Or.inl h)).elim
  · exact (hout (Or.inr (Or.inl h))).elim
  · exact Or.inl h
  · exact Or.inr h
  · exact (hout (Or.inr (Or.inr (Or.inl h)))).elim
  · exact (hout (Or.inr (Or.inr (Or.inr h)))).elim

theorem fan_outside_opposite_diagonal (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ) {z : Space 5}
    (hz : z ∈ actualPolygonFanVertices hP D v)
    (hout : z ∉ (T.figureFacet hP T.opposite).extremePoints ℝ) :
    ∃ u, Edge G v u ∧ dist z u = Real.sqrt (1 + CaseB.chord n) := by
  have hn' : (17 : ℝ) ≤ n := by exact_mod_cast hn
  rcases T.fan_outside_opposite hP hG hn hvG hz hout with rfl | rfl
  · refine ⟨T.base.b, (T.base.polygon_neighbors _).mpr (Or.inr rfl), ?_⟩
    rw [dist_comm]
    exact CaseB.case_dist_eq_sqrt_of_sq_eq (CaseB.case_antiprism_diagonal_sq_nonneg hn')
      T.base.diagonal_bx
  · refine ⟨T.base.a, (T.base.polygon_neighbors _).mpr (Or.inl rfl), ?_⟩
    rw [dist_comm]
    exact CaseB.case_dist_eq_sqrt_of_sq_eq (CaseB.case_antiprism_diagonal_sq_nonneg hn')
      T.base.diagonal_ay

end Uniform5.Composition.TypeIIActualFanData
