import Uniform5.CompositionLabeledFigureTemplates
import Uniform5.CompositionFigureEdgeCycle
import Uniform5.CompositionSignatures
import Uniform5.CompositionLongEdges

/-! The geometric conditions (a)--(d) and the signature-only S2 interface.
No realization uniqueness or producer-branch coverage is included. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Untrusted geometry and labels. Actual face, metric and incidence
requirements are stated in StageTwoFigureConditions. -/
structure StageTwoFigureData where
  carrier : Set (Space 4)
  facetLabel : Set (Space 4) → CanonicalFacetName
  cellLabel : Set (Space 4) → CellType
  edgeWord : Set (Space 4) → LibraryCycleWord

/-- Precisely the geometric vertex-figure requirements of stage two.
Template matches preserve cell labels under a single isometry per facet.
Complete edge cycles retain the geometric meaning of the polygon size. -/
structure StageTwoFigureConditions (N : LibraryNumericalData) (S : StageOneNumericalData)
    (c : RootRegionClass S) (R : ℝ) (D : StageTwoFigureData) : Prop where
  polytope : FinitePolytope D.carrier
  dimension : affineDimension D.carrier = 4
  sphere : ∀ x ∈ D.carrier.extremePoints ℝ,
    ‖x‖ = Real.sqrt (1 - 1 / (4 * R ^ 2))
  facet_type : ∀ F, Facet D.carrier F →
    LabeledFacetTemplateMatch N (D.facetLabel F) F D.cellLabel
  facet_occurs : ∀ F, Facet D.carrier F →
    ∃ W ∈ filteredClassCycles N S c, ∃ i, W.word.facet i = D.facetLabel F
  facet_offset : ∀ F, Facet D.carrier F →
    Metric.infDist (0 : Space 4) (affineSpan ℝ F : Set (Space 4)) =
      Real.sqrt ((Real.sqrt (1 - 1 / (4 * R ^ 2))) ^ 2 -
        (Real.sqrt (1 - 1 / (4 * intrinsicRadius (N.model (D.facetLabel F)) ^ 2))) ^ 2)
  facet_inner : ∀ F, Facet D.carrier F →
    ∃ L : Space 4 →L[ℝ] ℝ, ∃ t : ℝ,
      (∀ x ∈ D.carrier, L x ≤ t) ∧ F = {x ∈ D.carrier | L x = t} ∧ L 0 < t
  ridge_type : ∀ H, IsConvexFace D.carrier H → H.Nonempty → affineDimension H = 2 →
    Congruent H (cellFigureModel (D.cellLabel H))
  ridge_incidence : ∀ H, IsConvexFace D.carrier H → H.Nonempty → affineDimension H = 2 →
    TwoContainingFacets D.carrier H
  edge_cycle : ∀ e, IsConvexFace D.carrier e → e.Nonempty → affineDimension e = 1 →
    ∃ A : ActualEdgeIncidenceCycle D.carrier e (D.edgeWord e).length.val,
      (∀ i, D.facetLabel (A.facet i) = (D.edgeWord e).word.facet i) ∧
      (∀ i : Fin (D.edgeWord e).length.val,
        D.cellLabel (A.ridge i) = (D.edgeWord e).word.cell i)
  edge_word : ∀ e, IsConvexFace D.carrier e → e.Nonempty → affineDimension e = 1 →
    ∃ W ∈ filteredClassCycles N S c, (D.edgeWord e).classCode = W.classCode
  edge_polygon : ∀ e, IsConvexFace D.carrier e → e.Nonempty → affineDimension e = 1 →
    ∃ x y, Edge D.carrier x y ∧ e = segment ℝ x y ∧
      dist x y = CaseB.chord (D.edgeWord e).polygon.val
  separation : ∀ x ∈ D.carrier.extremePoints ℝ, ∀ y ∈ D.carrier.extremePoints ℝ,
    x ≠ y → 1 ≤ dist x y

noncomputable def StageTwoFigureData.signature {N : LibraryNumericalData}
    {S : StageOneNumericalData} {c : RootRegionClass S} {R : ℝ}
    (D : StageTwoFigureData) (hD : StageTwoFigureConditions N S c R D) : VertexFigureSignature :=
  geometricFigureSignature D.carrier hD.polytope D.facetLabel (fun e => (D.edgeWord e).classCode)

/-- The total number of signatures across the surviving classes. -/
noncomputable def stageTwoSignatureCount (N : LibraryNumericalData) (S : StageOneNumericalData)
    (T : StageTwoNumericalData S) : ℕ :=
  (survivingRootClasses N S).attach.sum fun c =>
    (T.signatures ⟨c.val, (Finset.mem_filter.mp c.property).1⟩).card

/-- The triangle word identifying the paper's empty class: three 5-cells
and a 16-cell. Ring indices use the pinned concrete library convention. -/
noncomputable def emptyStageTwoClassWord (W : LibraryCycleWord) : Prop :=
  W.polygon.val = 3 ∧
    Finset.univ.val.map W.word.facet =
      {canonicalFacetIndex (.wythoff 0 0), canonicalFacetIndex (.wythoff 0 0),
        canonicalFacetIndex (.wythoff 0 0), canonicalFacetIndex (.wythoff 1 7)}

/-- The coverage projection of computation S2: complete finite signature
output for all radii in each surviving class, 629 signatures altogether
and the stated unique empty class. Coverage identifies only a signature,
never a realization or producer branch. Retaining a signature does not
assert existence of an exact geometric figure with that signature. -/
structure S2 (N : LibraryNumericalData) (S : StageOneNumericalData)
    (T : StageTwoNumericalData S) : Prop where
  signature_count : stageTwoSignatureCount N S T = 629
  complete : ∀ c : ActiveRootClass S, c.val ∈ survivingRootClasses N S →
    ∀ R ∈ radiusClassRegion S c, ∀ D (hD : StageTwoFigureConditions N S c.val R D),
      D.signature hD ∈ T.signatures c
  empty_class : ∃ c : ActiveRootClass S, c.val ∈ survivingRootClasses N S ∧
    T.signatures c = ∅ ∧
    (∀ d : ActiveRootClass S, d.val ∈ survivingRootClasses N S → T.signatures d = ∅ → d = c) ∧
    ∃ W ∈ rootClassCycles S c.val, emptyStageTwoClassWord W

end Uniform5.Composition
