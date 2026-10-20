import Uniform5.CompositionSingleTypeIProduct
import Uniform5.CompositionSingleTypeIIProduct
import Uniform5.CompositionSingleTypeIIIExclusion

/-! The complete one-large-polygon branch. The actual incidence cycle
and its exhaustive F5 alternatives are constructed inside the proof. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_single_large_polygon_mem_K3
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ)
    (hu : UniqueLargeFaceAt P v G) : K3 P := by
  obtain ⟨D, _⟩ := unitUniform5_stage1_geometry hP hG
  have hvP := hG.1.2.extremePoints_subset_extremePoints hvG
  rcases D.nonexceptional_cycle_types classification4D hP hG
    (large_polygon_nonexceptional hn) with hI | hII | hIII
  · exact unitUniform5_single_typeI_mem_K3 classification3D classification4D
      N S hLIB hS1 hB2 hP hG hn hvP hvG hu D hI
  · exact unitUniform5_single_typeII_mem_K3 classification3D classification4D
      N S hLIB hS1 hB2 hP hG hn hvP hvG hu D hII
  · exact (D.typeIII_single_impossible classification3D classification4D
      N S hLIB hS1 hB2 hP hG hn hvG hu hIII).elim

end Uniform5.Composition
