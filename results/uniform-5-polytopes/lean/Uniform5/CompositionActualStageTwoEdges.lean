import Uniform5.CompositionActualEdgeWords
import Uniform5.CompositionNormalizedLabels
import Uniform5.CompositionStageTwoInputs

/-! The actual normalized figure satisfies the three stage-two edge
requirements with its single shared facet, cell and edge-word maps. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

/-- Retain the representative of exactly the same selected geometric
word as actualNormalizedEdgeWord, so its actual cycle remains available. -/
noncomputable def actualNormalizedRawEdgeWord (N : LibraryNumericalData)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (v : Space 5)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) (Q e : Set (Space 4)) : LibraryCycleWord :=
  if h : Nonempty (ActualNormalizedEdgeData N hP v f Q e)
  then (Classical.choice h).cycle.word
  else ⟨⟨3, by decide⟩, ⟨3, by decide⟩,
    ⟨fun _ => canonicalFacetIndex (.wythoff 0 0), fun _ => cellType ∅⟩⟩

theorem actualNormalizedRawEdgeWord_class (N : LibraryNumericalData)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (v : Space 5)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) (Q e : Set (Space 4)) :
    (actualNormalizedRawEdgeWord N hP v f Q e).classCode =
      actualNormalizedEdgeWord N hP v f Q e := by
  unfold actualNormalizedRawEdgeWord actualNormalizedEdgeWord
  split_ifs <;> rfl

/-- Geometry and labels only: validity of every field is proved separately,
and the data definition contains no stage-two coverage statement. -/
noncomputable def actualNormalizedStageTwoFigure (N : LibraryNumericalData)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (v : Space 5)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) (Q : Set (Space 4)) : StageTwoFigureData where
  carrier := Q
  facetLabel := normalizedFigureFacetLabel N P v
    (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) f
  cellLabel := normalizedFigureCellLabel P v
    (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) f
  edgeWord := actualNormalizedRawEdgeWord N hP v f Q

namespace ActualNormalizedEdgeData
variable {N : LibraryNumericalData} {P : Set (Space 5)} {hP : UnitUniform 5 P}
  {v : Space 5} {f : Space 4 →ᵃⁱ[ℝ] Space 5} {Q e : Set (Space 4)}
  (D : ActualNormalizedEdgeData N hP v f Q e)

theorem incidenceCycle_facet_label
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) (i : Fin D.cycle.cycle.length) :
    (actualNormalizedStageTwoFigure N hP v f Q).facetLabel ((D.incidenceCycle him).facet i) =
      D.cycle.word.word.facet i := by
  change parentFigureFacetLabel N P v _ (f '' (D.incidenceCycle him).facet i) =
    D.cycle.labels.facetLabel i
  rw [D.incidenceCycle_facet_image him]
  have hvP := D.polygon_face.1.2.extremePoints_subset_extremePoints D.apex
  rw [parentFigureFacetLabel_section (n := 2) hP hvP
    (D.cycle.cycle.facet_incidence i).1.1 ((D.cycle.cycle.facet_incidence i).2.1 D.apex.1)]
  exact (D.facet_labels i).symm

theorem incidenceCycle_cell_label
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) (i : Fin D.cycle.cycle.length) :
    (actualNormalizedStageTwoFigure N hP v f Q).cellLabel ((D.incidenceCycle him).ridge i) =
      D.cycle.word.word.cell i := by
  change parentFigureCellLabel P v _ (f '' (D.incidenceCycle him).ridge i) =
    D.cycle.labels.cellLabel i
  rw [D.incidenceCycle_ridge_image him]
  have hvP := D.polygon_face.1.2.extremePoints_subset_extremePoints D.apex
  rw [parentFigureCellLabel_section (n := 2) hP hvP (D.cycle.cycle.cell_face i)
    (D.cycle.cycle.cell_contains i D.apex.1)]
  exact (D.cell_labels i).symm

end ActualNormalizedEdgeData

section Actual
variable (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
  {P : Set (Space 5)} (hP : UnitUniform 5 P) (hsmall : SmallFaces P)
  {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
  (N : LibraryNumericalData) (hLIB : LIB N)
  (f : Space 4 →ᵃⁱ[ℝ] Space 5) {Q : Set (Space 4)} (hQ : FinitePolytope Q)
  (him : f '' Q = vertexFigure P v
    (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))

include classification3D classification4D hsmall hv hLIB hQ him

theorem actualNormalizedRawEdgeWord_witness {e : Set (Space 4)}
    (he : IsConvexFace Q e) (hne : e.Nonempty) (hd : affineDimension e = 1) :
    ∃ D : ActualNormalizedEdgeData N hP v f Q e,
      actualNormalizedRawEdgeWord N hP v f Q e = D.cycle.word := by
  have hh := exists_actualNormalizedEdgeData classification3D classification4D
    hP hsmall hv N hLIB f hQ him he hne hd
  exact ⟨Classical.choice hh, by rw [actualNormalizedRawEdgeWord, dif_pos hh]⟩

theorem actualNormalizedStageTwo_edge_cycle {e : Set (Space 4)}
    (he : IsConvexFace Q e) (hne : e.Nonempty) (hd : affineDimension e = 1) :
    let D := actualNormalizedStageTwoFigure N hP v f Q
    ∃ A : ActualEdgeIncidenceCycle Q e (D.edgeWord e).length.val,
      (∀ i, D.facetLabel (A.facet i) = (D.edgeWord e).word.facet i) ∧
      (∀ i : Fin (D.edgeWord e).length.val,
        D.cellLabel (A.ridge i) = (D.edgeWord e).word.cell i) := by
  obtain ⟨A, hA⟩ := actualNormalizedRawEdgeWord_witness classification3D classification4D
    hP hsmall hv N hLIB f hQ him he hne hd
  dsimp only [actualNormalizedStageTwoFigure]
  rw [hA]
  exact ⟨A.incidenceCycle him, A.incidenceCycle_facet_label him, A.incidenceCycle_cell_label him⟩

theorem actualNormalizedStageTwo_edge_word (S : StageOneNumericalData) (hS : S1 N S)
    {j : RetainedRootIndex S}
    (hj : intrinsicRadius P ∈ positiveReciprocalRegion (retainedRootInterval S j))
    {e : Set (Space 4)} (he : IsConvexFace Q e) (hne : e.Nonempty) (hd : affineDimension e = 1) :
    ∃ W ∈ filteredClassCycles N S ((retainedRootGraph S).connectedComponentMk j),
      ((actualNormalizedStageTwoFigure N hP v f Q).edgeWord e).classCode = W.classCode := by
  obtain ⟨A, hA⟩ := actualNormalizedRawEdgeWord_witness classification3D classification4D
    hP hsmall hv N hLIB f hQ him he hne hd
  change ∃ W : LibraryCycleWord, W ∈ _ ∧
    (actualNormalizedRawEdgeWord N hP v f Q e).classCode = W.classCode
  rw [hA]
  exact A.filtered hsmall classification3D classification4D S hLIB hS hj

theorem actualNormalizedStageTwo_edge_polygon {e : Set (Space 4)}
    (he : IsConvexFace Q e) (hne : e.Nonempty) (hd : affineDimension e = 1) :
    ∃ x y, Edge Q x y ∧ e = segment ℝ x y ∧
      dist x y = CaseB.chord ((actualNormalizedStageTwoFigure N hP v f Q).edgeWord e).polygon.val := by
  obtain ⟨A, hA⟩ := actualNormalizedRawEdgeWord_witness classification3D classification4D
    hP hsmall hv N hLIB f hQ him he hne hd
  change ∃ x y, Edge Q x y ∧ e = segment ℝ x y ∧
    dist x y = CaseB.chord (actualNormalizedRawEdgeWord N hP v f Q e).polygon.val
  rw [hA]
  exact A.chord

theorem actualNormalizedStageTwo_radiusCompatible :
    (geometricFigureSignature Q hQ (actualNormalizedStageTwoFigure N hP v f Q).facetLabel
      (fun e => ((actualNormalizedStageTwoFigure N hP v f Q).edgeWord e).classCode)).RadiusCompatible
      N (intrinsicRadius P) := by
  have heq : (fun e => ((actualNormalizedStageTwoFigure N hP v f Q).edgeWord e).classCode) =
      actualNormalizedEdgeWord N hP v f Q := by
    funext e
    exact actualNormalizedRawEdgeWord_class N hP v f Q e
  rw [heq]
  exact actualNormalizedFigureSignature_radiusCompatible classification3D classification4D
    hP hsmall hv N hLIB f hQ him _

end Actual
end Uniform5.Composition
