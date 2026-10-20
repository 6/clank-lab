import Uniform5.CompositionTypeIIFanCellTransport
import Uniform5.CompositionMixedAntiprismUniqueness

/-! The surviving actual Type I / Type II pair belongs to K3. The
antiprism cell is uniquely selected by actual incidence and transports
as a whole face across every edge; no product structure is assumed. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_paired_mixed_mem_K3
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G H K : Set (Space 5)} (hP : UnitUniform 5 P) {n m : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n) (hH : PolygonFace P H m) (hm : 17 ≤ m)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ) (hvH : v ∈ H.extremePoints ℝ)
    (hGH : G ≠ H) (hcover : TwoLargeFacesCoverAt P v G H)
    (hK : Facet P K) (hGK : G ⊆ K) (hHK : H ⊆ K)
    (D : ActualPolygonCycle P G) (A : ActualPolygonCycle P H)
    (hI : D.CaseBTypeI n) (hII : A.CaseBTypeII m) : K3 P := by
  obtain ⟨U⟩ := A.typeII_actual_fan hP hH hm hvH hII
  apply unitUniform5_mem_K3_of_unique_root_cell hP (A.cell_face U.anti)
    (A.cell_dimension U.anti) (hG.1.2.extremePoints_subset_extremePoints hvG)
    (A.cell_contains U.anti hvH.1)
  · intro F hF hvF hFC
    exact unitUniform5_mixed_antiprism_model_unique classification4D hP hG hH hm hvG
      hcover D hI (A.cell_face U.anti) (A.cell_contains U.anti) (A.cell_dimension U.anti)
      U.antiprism hF hvF hFC
  · intro w hw
    have hfan := unitUniform5_paired_mixed_typeII_vertex_cover classification3D classification4D
      N S hLIB hS1 hB2 hP hG hn hH hm hvG hvH hGH hcover hK hGK hHK D A hI hII hw
    obtain ⟨d, hd, hF, hFA, hwF⟩ := U.fan_vertex_cell_translate hP hH hm hvH hfan
    exact ⟨d, hd, hF, congruent_trans hFA (congruent_symm U.antiprism), hwF⟩

end Uniform5.Composition
