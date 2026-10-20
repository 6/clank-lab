import Uniform5.CompositionCaseAClassification
import Uniform5.CompositionCaseBClassification
import Uniform5.CompositionProducerStageThreeInputs
import Uniform5.CompositionRidgeListInputs
import Uniform5.CompositionFilterClasses

/-! The paper's main classification as an actual geometric theorem,
conditional on its individually named computations and cited lower-
dimensional classifications. No case conclusion or geometric realization
constructor is added beyond the explicitly named U3 computations. -/
noncomputable section
namespace Uniform5.Composition

/-- The logical core uses the independent U3 route for Case A and the
actual single/paired-fan proofs for Case B. -/
theorem classification_of_core_inputs
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (T : StageTwoNumericalData S)
    (U : U3RealizationData S) (M : U3KnownModelData) (D : U3ForcingData)
    (extra : U3StarData)
    (hLIB : LIB N) (hS1 : S1 N S) (hS2 : S2 N S T) (hROOT : ROOT N S T)
    (hDEV : DEV N S U extra) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP1 : CaseB.P1) (hW : Wedge.W hP1) (hPartner : CaseB.PartnerRadiusFilter)
    (hU3Realization : U3Realizations N S T U)
    (hU3Identification : U3Identification N S U M)
    (hU3Forcing : U3Forcing N S U D) : MainClassification := by
  intro P hP
  rcases smallFaces_or_largeFace P with hsmall | hlarge
  · exact unitUniform5_smallFaces_known classification3D classification4D N S T U M D
      extra hLIB hS1 hS2 hROOT hB2 hU3Realization hU3Identification hU3Forcing hDEV hP hsmall
  · exact unitUniform5_largeFace_known classification3D classification4D N S hLIB hS1 hB2
      hP1 hPartner hW hP hlarge

/-- Main classification with exactly the twelve computational premises used by the proof. -/
theorem mainClassification
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (T : StageTwoNumericalData S)
    (U : U3RealizationData S) (M : U3KnownModelData) (D : U3ForcingData)
    (extra : U3StarData)
    (hLIB : LIB N) (hS1 : S1 N S) (hS2 : S2 N S T) (hROOT : ROOT N S T)
    (hDEV : DEV N S U extra) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP1 : CaseB.P1) (hW : Wedge.W hP1) (hPartner : CaseB.PartnerRadiusFilter)
    (hU3Realization : U3Realizations N S T U)
    (hU3Identification : U3Identification N S U M)
    (hU3Forcing : U3Forcing N S U D) :
    ∀ P : Set (Space 5), UnitUniform 5 P → K1 P ∨ K2 P ∨ K3 P :=
  classification_of_core_inputs classification3D classification4D N S T U M D extra
    hLIB hS1 hS2 hROOT hDEV hB2 hP1 hW hPartner hU3Realization hU3Identification hU3Forcing

end Uniform5.Composition
