import Uniform5.CompositionActualStageTwoEdges
import Uniform5.CompositionActualFacetOccurrence
import Uniform5.CompositionNormalizedFigurePlacement
import Uniform5.CompositionRootInput

/-! Composition through S2 for actual small-faced unit-uniform five-polytopes.
All figure geometry and labels are constructed before signature coverage is used. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- All of (a)--(d) hold in any centered intrinsic realization of the actual
figure. The normalization premises are discharged in the theorem below. -/
theorem actualNormalizedStageTwo_conditions
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (hLIB : LIB N) (hS : S1 N S)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) {Q : Set (Space 4)} (hQ : FinitePolytope Q)
    (hdQ : affineDimension Q = 4) (h0 : (0 : Space 4) ∈ intrinsicInterior ℝ Q)
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
    (hf0 : f 0 = vertexCentroid (vertices P (uniform_finitePolytope hP.1)) +
      figureCenter (v - vertexCentroid (vertices P (uniform_finitePolytope hP.1))) (intrinsicRadius P))
    (hsphere : ∀ x ∈ Q.extremePoints ℝ, ‖x‖ = Real.sqrt (1 - 1 / (4 * intrinsicRadius P ^ 2)))
    (hsep : ∀ x ∈ Q.extremePoints ℝ, ∀ y ∈ Q.extremePoints ℝ, x ≠ y → 1 ≤ dist x y)
    {j : RetainedRootIndex S}
    (hj : intrinsicRadius P ∈ positiveReciprocalRegion (retainedRootInterval S j)) :
    StageTwoFigureConditions N S ((retainedRootGraph S).connectedComponentMk j)
      (intrinsicRadius P) (actualNormalizedStageTwoFigure N hP v f Q) where
  polytope := hQ
  dimension := hdQ
  sphere := hsphere
  facet_type := fun F hF => actual_normalized_facet_template
    classification3D classification4D hP hs hv N hLIB f him hF
  facet_occurs := fun F hF => normalizedFigureFacetLabel_occurs
    classification3D classification4D hP hs hv N S hLIB hS f him hF hj
  facet_offset := fun F hF => actual_normalized_facet_offset
    classification3D classification4D hP hs hv N hLIB f him hf0 hF
  facet_inner := fun F hF => facet_strict_support_of_intrinsicInterior hQ hF h0
  ridge_type := fun H hH hne hd => actual_normalized_ridge_template hP hv f him hH hne hd
  ridge_incidence := fun H hH hne hd => finitePolytope_ridge_two_facets hQ hH hne (by
    change affineDimension H + 2 = affineDimension Q
    rw [hd, hdQ])
  edge_cycle := fun e he hne hd => actualNormalizedStageTwo_edge_cycle
    classification3D classification4D hP hs hv N hLIB f hQ him he hne hd
  edge_word := fun e he hne hd => actualNormalizedStageTwo_edge_word
    classification3D classification4D hP hs hv N hLIB f hQ him S hS hj he hne hd
  edge_polygon := fun e he hne hd => actualNormalizedStageTwo_edge_polygon
    classification3D classification4D hP hs hv N hLIB f hQ him he hne hd
  separation := hsep

/-- Actual Case A polytopes have a listed signature, with its real geometry
and all edge closure equations. Only the named cited/LIB/S1/S2 inputs occur;
there is no supplied figure, catalogue coverage, or realization hypothesis. -/
theorem unitUniform5_smallFaces_stageTwo
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (T : StageTwoNumericalData S)
    (hLIB : LIB N) (hS : S1 N S) (hS2 : S2 N S T) :
    ∃ c : ActiveRootClass S, c.val ∈ survivingRootClasses N S ∧
      intrinsicRadius P ∈ radiusClassRegion S c ∧
      ∃ (f : Space 4 →ᵃⁱ[ℝ] Space 5) (Q : Set (Space 4)),
        f '' Q = vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) ∧
        ∃ hD : StageTwoFigureConditions N S c.val (intrinsicRadius P)
            (actualNormalizedStageTwoFigure N hP v f Q),
          (actualNormalizedStageTwoFigure N hP v f Q).signature hD ∈ T.signatures c ∧
          ((actualNormalizedStageTwoFigure N hP v f Q).signature hD).RadiusCompatible
            N (intrinsicRadius P) := by
  classical
  obtain ⟨_, j, hj, hc, _⟩ := unitUniform5_smallFaces_first_stage
    classification3D classification4D hP hs N S hLIB hS hv
  let c : ActiveRootClass S := ⟨_, (Finset.mem_filter.mp hc).1⟩
  have hR : intrinsicRadius P ∈ radiusClassRegion S c := radius_mem_classRegion S c rfl hj
  obtain ⟨f, Q, him, hf0, _, hQ, hdQ, h0, _, _, hsphere, hsep⟩ :=
    unitUniform5_vertexFigure_centered_model hP hv
  let hD := actualNormalizedStageTwo_conditions classification3D classification4D
    hP hs hv N S hLIB hS f hQ hdQ h0 him hf0 hsphere hsep hj
  refine ⟨c, hc, hR, f, Q, him, hD, hS2.complete c hc _ hR _ hD, ?_⟩
  exact actualNormalizedStageTwo_radiusCompatible
    classification3D classification4D hP hs hv N hLIB f hQ him

/-- Combining the exact S2 and ROOT inputs now supplies positive class
endpoints for an actual polytope, not just a hypothetical signature. -/
theorem unitUniform5_smallFaces_positive_class
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (T : StageTwoNumericalData S)
    (hLIB : LIB N) (hS : S1 N S) (hS2 : S2 N S T) (hROOT : ROOT N S T) :
    ∃ c : ActiveRootClass S, c.val ∈ survivingRootClasses N S ∧
      intrinsicRadius P ∈ radiusClassRegion S c ∧ 0 < (reciprocalClassHull S c).lo := by
  obtain ⟨c, hc, hR, _, _, _, hD, hσ, _⟩ := unitUniform5_smallFaces_stageTwo
    classification3D classification4D hP hs hv N S T hLIB hS hS2
  exact ⟨c, hc, hR, hROOT.class_lower_pos c hc hσ⟩

end Uniform5.Composition
