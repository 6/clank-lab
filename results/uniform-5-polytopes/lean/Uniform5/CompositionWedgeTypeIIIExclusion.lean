import Uniform5.CompositionWedgeTypeIIIUse
import Uniform5.CompositionSingleTypeIIIExclusion

/-! The Type III case is excluded from the exact named computations and
actual geometry. The necessary single-face cover follows from W. -/
noncomputable section
namespace Uniform5.Composition.ActualPolygonCycle
open Set
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

theorem typeIII_impossible
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (p1 : CaseB.P1) (hW : Wedge.W p1)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    {v : Space 5} (hv : v ∈ G.extremePoints ℝ) (hIII : D.CaseBTypeIII n) : False := by
  obtain ⟨T⟩ := D.typeIII_actual_fan hP hG hn hv hIII
  exact D.typeIII_single_impossible classification3D classification4D N S hLIB hS1 hB2
    hP hG hn hv (T.uniqueLargeFaceAt p1 hW hP hG hn hv) hIII

end Uniform5.Composition.ActualPolygonCycle
