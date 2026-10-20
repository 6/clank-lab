import Uniform5.CompositionSimpleCellNeighborChart
import Uniform5.CompositionThreeFaceUniqueness

/-! Actual cells in a duoprism have one lateral neighbor at a specified
polygon vertex; different actual cells give different lateral points. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem unitUniform4_duoprism_cell_third_neighbor {K C G : Set E}
    {v a b : E} {n q : ℕ} (hK : UnitUniform 4 K)
    (hn : 3 ≤ n) (hq : 3 ≤ q) (hn4 : n ≠ 4)
    (hmodel : Congruent K (duoprismModel n q))
    (hG : PolygonFace K G n) (hv : v ∈ G.extremePoints ℝ)
    (hC : Facet K C) (hGC : G ⊆ C)
    (hpair : ∀ w, Edge G v w ↔ w = a ∨ w = b) (hab : a ≠ b) :
    ∃ z, z ∈ C ∧ z ∉ G ∧ z ≠ a ∧ z ≠ b ∧
      ∀ w, Edge C v w ↔ w = a ∨ w = b ∨ w = z := by
  have hKC := uniform_finitePolytope hK.1
  have hCC := finitePolytope_face hKC hC.1 hC.2.1
  have hGCface := face_restrict hG.1 hC.1.2.1 hGC
  have haG := (hpair a).mpr (Or.inl rfl)
  have hbG := (hpair b).mpr (Or.inr rfl)
  have haC := (edge_face_iff hCC hGCface hv.1 haG.2.1.1).mpr haG
  have hbC := (edge_face_iff hCC hGCface hv.1 hbG.2.1.1).mpr hbG
  have hvK := hG.1.2.extremePoints_subset_extremePoints hv
  obtain ⟨T⟩ := unitUniform4_duoprism_neighbor_chart_parameters hK hn hq hmodel hG hn4 hv
  obtain ⟨z, hza, hzb, hz⟩ := finitePolytope_simpleFacet_third_neighbor hKC
    (uniform_dimension hK.1) hvK (T.neighbour_card hK hvK) hC haC hbC hab
  have hez := (hz z).mpr (Or.inr (Or.inr rfl))
  refine ⟨z, hez.2.1.1, ?_, hza, hzb, hz⟩
  intro hzG
  have heG := (edge_face_iff hCC hGCface hv.1 hzG).mp hez
  exact ((hpair z).mp heG).elim hza hzb

/-- The common polygon and true face dimensions prevent any two
lateral chart points from being identified across distinct cells. -/
theorem actual_cell_lateral_points_ne {P G C D : Set E} {z w : E}
    (hG : IsConvexFace P G) (hC : IsConvexFace P C) (hD : IsConvexFace P D)
    (hne : G.Nonempty) (hGC : G ⊆ C) (hGD : G ⊆ D)
    (hdG : affineDimension G = 2) (hdC : affineDimension C = 3)
    (hdD : affineDimension D = 3) (hneCD : C ≠ D)
    (hzC : z ∈ C) (hwD : w ∈ D) (hzG : z ∉ G) : z ≠ w := by
  intro he
  exact hneCD (three_faces_eq_of_common_point hG hC hD hne hGC hGD
    hdG hdC hdD hzC (he.symm ▸ hwD) hzG)

end Uniform5.Composition
