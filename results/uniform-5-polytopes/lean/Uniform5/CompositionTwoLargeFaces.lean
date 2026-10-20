import Uniform5.CompositionSingleFanCover
import Uniform5.CompositionLongEdges

/-! Distinct actual large polygons give disjoint long edges of the actual
vertex figure. This constructs the geometric witnesses for the multi-face case. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_two_large_faces_disjoint_edges
    {P G H : Set (Space 5)} (hP : UnitUniform 5 P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    {n m : ℕ} (hG : PolygonFace P G n) (hn : 17 ≤ n) (hvG : v ∈ G)
    (hH : PolygonFace P H m) (hm : 17 ≤ m) (hvH : v ∈ H) (hne : G ≠ H) :
    let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    ∃ a b c d : Space 5, Edge V a b ∧ Edge V c d ∧
      G ∩ V = segment ℝ a b ∧ H ∩ V = segment ℝ c d ∧
      dist a b = CaseB.chord n ∧ dist c d = CaseB.chord m ∧
      Disjoint ({a, b} : Set (Space 5)) {c, d} := by
  dsimp only
  obtain ⟨a, b, hab, hva, hvb, hsegG⟩ := unitUniform5_polygon_vertexFigure_edge hP hv hG hvG
  obtain ⟨c, d, hcd, hvc, hvd, hsegH⟩ := unitUniform5_polygon_vertexFigure_edge hP hv hH hvH
  have hdistG := polygonFace_neighbor_chord hP hG hva hvb hab.2.2.1
  have hdistH := polygonFace_neighbor_chord hP hH hvc hvd hcd.2.2.1
  have hsegs : segment ℝ a b ≠ segment ℝ c d := by
    intro he
    obtain ⟨F, _, hF⟩ := unitUniform5_vertexFigure_edge_unique_twoFace hP hv hab
    exact hne ((hF G ⟨hG.1, hvG, hG.2.1, hsegG⟩).trans
      (hF H ⟨hH.1, hvH, hH.2.1, hsegH.trans he.symm⟩).symm)
  have hlongG : CaseB.chord 17 ≤ dist a b := by
    rw [hdistG]
    exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hn)
  have hlongH : CaseB.chord 17 ≤ dist c d := by
    rw [hdistH]
    exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hm)
  refine ⟨a, b, c, d, hab, hcd, hsegG, hsegH, hdistG, hdistH,
    unitUniform5_long_edges_disjoint hP hv hab hcd hlongG hlongH ?_ ?_⟩
  · rintro ⟨rfl, rfl⟩
    exact hsegs rfl
  · rintro ⟨rfl, rfl⟩
    exact hsegs (segment_symm ℝ _ _)

/-- Failure of the one-large-face condition supplies a second genuine
polygon through the same vertex, without a supplied list of face labels. -/
theorem not_uniqueLargeFaceAt_witness {P G : Set (Space 5)} {v : Space 5}
    (hu : ¬ UniqueLargeFaceAt P v G) :
    ∃ H m, PolygonFace P H m ∧ 17 ≤ m ∧ v ∈ H.extremePoints ℝ ∧ H ≠ G := by
  classical
  unfold UniqueLargeFaceAt at hu
  push_neg at hu
  exact hu

end Uniform5.Composition
