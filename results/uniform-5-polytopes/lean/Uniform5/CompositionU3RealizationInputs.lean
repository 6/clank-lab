import Uniform5.CompositionU3StarData
import Uniform5.CompositionU3ReportP16

/-! Named realization computation of section U3. The report contains row
indices and counts; the placements and exact canonical encodings belong to
the search's internal states. Their interpretation is explicitly part of
this input, never inferred from an interval overlap or a printed count. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Untrusted decoding of report indices and internal exact encodings.
There is deliberately no geometric correctness field in this data. -/
structure U3RealizationData (S : StageOneNumericalData) where
  classOf : ℕ → ActiveRootClass S
  signatureOf : ℕ → ℕ → VertexFigureSignature
  rowEncoding : U3ReportRow → U3Encoding
  canonicalEncoding : U3StarData → U3Encoding

def U3RealizationData.rowClass {S : StageOneNumericalData}
    (U : U3RealizationData S) (r : U3ReportRow) : ActiveRootClass S :=
  U.classOf r.classIndex

def U3RealizationData.rowSignature {S : StageOneNumericalData}
    (U : U3RealizationData S) (r : U3ReportRow) : VertexFigureSignature :=
  U.signatureOf r.classIndex r.figureIndex

/-- The coverage and grouping projection of section U3 step 1: exhaustive
geometric realization search and soundness of exact canonical grouping.
Rigidity is at a fixed radius; the separate ROOT input is required to
compare radii within one class. A retained row does not assert existence
of an exact geometric star or its extension to a uniform polytope. -/
structure U3Realizations (N : LibraryNumericalData) (S : StageOneNumericalData)
    (T : StageTwoNumericalData S) (U : U3RealizationData S) : Prop where
  class_valid : ∀ r ∈ u3ReportP16,
    (U.rowClass r).val ∈ survivingRootClasses N S
  class_indices : ∀ r ∈ u3ReportP16, ∀ s ∈ u3ReportP16,
    U.rowClass r = U.rowClass s → r.classIndex = s.classIndex
  signature_valid : ∀ r ∈ u3ReportP16,
    U.rowSignature r ∈ T.signatures (U.rowClass r)
  signature_complete : ∀ c : ActiveRootClass S,
    c.val ∈ survivingRootClasses N S → ∀ σ ∈ T.signatures c,
      ∃ r ∈ u3ReportP16, U.rowClass r = c ∧ U.rowSignature r = σ
  signature_indices : ∀ r ∈ u3ReportP16, ∀ s ∈ u3ReportP16,
    U.rowClass r = U.rowClass s → U.rowSignature r = U.rowSignature s →
      r.signatureIndex = s.signatureIndex
  complete : ∀ (c : ActiveRootClass S), c.val ∈ survivingRootClasses N S →
    ∀ X (hX : U3GeometricStar N S c.val X), X.radius ∈ radiusClassRegion S c →
      X.figure.signature hX.figure ∈ T.signatures c →
      ∃ r ∈ u3ReportP16, U.rowClass r = c ∧
        U.rowSignature r = X.figure.signature hX.figure ∧
        U.canonicalEncoding X = U.rowEncoding r
  encoding_rigid : ∀ (c : ActiveRootClass S), c.val ∈ survivingRootClasses N S →
    ∀ X Y, U3GeometricStar N S c.val X → U3GeometricStar N S c.val Y →
      X.radius ∈ radiusClassRegion S c → Y.radius ∈ radiusClassRegion S c →
      X.radius = Y.radius → U.canonicalEncoding X = U.canonicalEncoding Y →
        U3StarCongruent N X Y

/-- Whole-star rigidity follows from the realization computation once
the two stars have the same radius and reported canonical row. -/
theorem U3Realizations.same_row_congruent
    {N : LibraryNumericalData} {S : StageOneNumericalData}
    {T : StageTwoNumericalData S} {U : U3RealizationData S}
    (hU : U3Realizations N S T U) {r : U3ReportRow} (hr : r ∈ u3ReportP16)
    {X Y : U3StarData}
    (hX : U3GeometricStar N S (U.rowClass r).val X)
    (hY : U3GeometricStar N S (U.rowClass r).val Y)
    (hRX : X.radius ∈ radiusClassRegion S (U.rowClass r))
    (hRY : Y.radius ∈ radiusClassRegion S (U.rowClass r))
    (hR : X.radius = Y.radius)
    (hEX : U.canonicalEncoding X = U.rowEncoding r)
    (hEY : U.canonicalEncoding Y = U.rowEncoding r) : U3StarCongruent N X Y :=
  hU.encoding_rigid (U.rowClass r) (hU.class_valid r hr) X Y hX hY hRX hRY hR
    (hEX.trans hEY.symm)

/-- The concrete report has one realization row for each interpreted
signature; this finite uniqueness is not an additional assumption. -/
theorem U3Realizations.row_eq_of_signature
    {N : LibraryNumericalData} {S : StageOneNumericalData}
    {T : StageTwoNumericalData S} {U : U3RealizationData S}
    (hU : U3Realizations N S T U) {r s : U3ReportRow}
    (hr : r ∈ u3ReportP16) (hs : s ∈ u3ReportP16)
    (hc : U.rowClass r = U.rowClass s) (hσ : U.rowSignature r = U.rowSignature s) : r = s :=
  List.inj_on_of_nodup_map u3ReportP16_signature_indices_nodup hr hs
    (hU.signature_indices r hr s hs hc hσ)

end Uniform5.Composition
