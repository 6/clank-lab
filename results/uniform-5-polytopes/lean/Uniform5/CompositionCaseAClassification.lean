import Uniform5.CompositionU3KnownBranch
import Uniform5.CompositionU3DevelopmentInput

/-! The entire small-faced branch: actual geometry supplies a U3 row,
known rows are identified by elimination, and the extra row is refuted. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_smallFaces_known
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (T : StageTwoNumericalData S)
    (U : U3RealizationData S) (M : U3KnownModelData) (D : U3ForcingData)
    (extra : U3StarData)
    (hLIB : LIB N) (hS1 : S1 N S) (hS2 : S2 N S T) (hROOT : ROOT N S T)
    (hB2 : CaseB.B2 (stageOneOmega S))
    (hU : U3Realizations N S T U) (hI : U3Identification N S U M)
    (hF : U3Forcing N S U D) (hDEV : DEV N S U extra)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hsmall : SmallFaces P) : Known P := by
  obtain ⟨v, hv⟩ := finitePolytope_extremePoints_nonempty (uniform_finitePolytope hP.1)
  obtain ⟨c, hc, X, hxv, hxc, hxR, hxs, hX, hR, hσ, hcl⟩ :=
    unitUniform5_smallFaces_u3_star classification3D classification4D hP hsmall hv
      N S T hLIB hS1 hS2
  obtain ⟨r, hr, hrc, hrs, hre⟩ := hU.complete c hc X hX hR hσ
  have hX' : U3GeometricStar N S (U.rowClass r).val X := hrc.symm ▸ hX
  have hR' : X.radius ∈ radiusClassRegion S (U.rowClass r) := hrc.symm ▸ hR
  have hsig : X.figure.signature hX'.figure = U.rowSignature r := hrs.symm
  rcases u3ReportP16_mem_verdict hr with hk | href
  · exact u3_known_row_classifies classification3D classification4D N S T U M D
      hLIB hS1 hS2 hROOT hB2 hU hI hF hP hr hk hX'
      (hxv.symm ▸ hv) hxc (by simpa [hxv] using hxs) hR' hsig hcl hre
  · have heq := u3ReportP16_refuted_unique hr href
    subst r
    exact (hDEV.refuted_row_impossible hU hROOT hX' hR'
      (hsig ▸ hcl) hre ⟨P, hP⟩ hv hxv hxc hxs).elim

end Uniform5.Composition
