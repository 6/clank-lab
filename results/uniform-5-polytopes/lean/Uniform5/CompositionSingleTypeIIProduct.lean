import Uniform5.CompositionTypeIIFanNeighbors
import Uniform5.CompositionUniqueAntiprismCells

/-! Product reconstruction in the actual single-large-polygon Type II case. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_single_typeII_mem_K3
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (hvG : v ∈ G.extremePoints ℝ) (hu : UniqueLargeFaceAt P v G)
    (D : ActualPolygonCycle P G) (hII : D.CaseBTypeII n) : K3 P := by
  obtain ⟨a, ha, ht⟩ := D.typeII_root_cell_translates classification3D classification4D
    N S hLIB hS1 hB2 hP hG hn hvG hu hII
  let L := unitUniform5_uniqueLargeFaceSelection hP hG hv hvG hu
  let A := unitUniform5_antiprismCellSelection hP (D.cell_face a)
    (D.cell_dimension a) ha hv (D.cell_contains a hvG.1)
  have hac : D.cell a = A.cell v := A.unique_at_vertex classification4D L hP hn hv
    (D.cell_face a) (D.cell_contains a hvG.1) (D.cell_dimension a) ha
  apply A.mem_K3_of_root_lateral_cells classification4D L hP hn hv
  rwa [← hac]

end Uniform5.Composition
