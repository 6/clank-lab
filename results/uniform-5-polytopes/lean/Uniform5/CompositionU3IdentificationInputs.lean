import Uniform5.CompositionU3RealizationInputs
import Uniform5.CompositionKnownFiveNames
import Uniform5.CompositionU3ReportGroupsP16

/-! Named U3 identification-by-elimination computation. The literal model
construction and class-admission guards are explicit external properties.
The two exclusion statuses have separate soundness fields. MATCH is not
used as an equality certificate. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Raw geometric interpretations of listed construction names. No
uniformity, construction validity, or classification is included here. -/
structure U3KnownModelData where
  model : KnownFiveName → Set (Space 5)
  root : KnownFiveName → Space 5
  center : KnownFiveName → Space 5

/-- Matching means congruence of the full incident facets with the root
and center fixed as prescribed, not equality of rounded coordinates. -/
def U3MatchesKnown (N : LibraryNumericalData) (M : U3KnownModelData)
    (n : KnownFiveName) (X : U3StarData) : Prop :=
  ∃ g : Space 5 ≃ᵃⁱ[ℝ] Space 5,
    g X.root = M.root n ∧ g X.center = M.center n ∧
      facetSetImage g (X.star N) = facetStar (M.model n) (M.root n)

/-- Section U3 step 3. `admitted` is the exact construction/class guard:
the listed unit-uniform model has radius inside the class, and every facet
type occurs in the input library. It is not a conclusion of the Lean name
decoder. The NO and NO-COUNT checks exclude whole-star matches; their
frame and neighbour-count computations remain outside Lean. -/
structure U3Identification (N : LibraryNumericalData) (S : StageOneNumericalData)
    (U : U3RealizationData S) (M : U3KnownModelData) : Prop where
  admitted : ∀ r ∈ u3ReportP16, ∀ n : KnownFiveName,
    n.sourceName ∈ r.known_names →
      KnownFiveModel n (M.model n) ∧
      ∃ hQ : UnitUniform 5 (M.model n),
        M.root n ∈ (M.model n).extremePoints ℝ ∧
        M.center n = vertexCentroid (vertices (M.model n) (uniform_finitePolytope hQ.1)) ∧
        intrinsicRadius (M.model n) ∈ radiusClassRegion S (U.rowClass r) ∧
        ∀ F, Facet (M.model n) F →
          ∃ s ∈ u3ReportP16, ∃ k ∈ (U.rowSignature s).facets, Congruent F (N.model k)
  soundNO : ∀ r ∈ u3ReportP16, ∀ n : KnownFiveName,
    (n.sourceName, U3EmbeddingVerdict.no) ∈ r.embedding →
      ∀ X, U3GeometricStar N S (U.rowClass r).val X →
        X.radius ∈ radiusClassRegion S (U.rowClass r) →
        U.canonicalEncoding X = U.rowEncoding r → ¬ U3MatchesKnown N M n X
  soundNOCOUNT : ∀ r ∈ u3ReportP16, ∀ n : KnownFiveName,
    (n.sourceName, U3EmbeddingVerdict.noCount) ∈ r.embedding →
      ∀ X, U3GeometricStar N S (U.rowClass r).val X →
        X.radius ∈ radiusClassRegion S (U.rowClass r) →
        U.canonicalEncoding X = U.rowEncoding r → ¬ U3MatchesKnown N M n X

/-- An excluded realization cannot be the star of the admitted model.
This theorem uses only the two negative statuses, never MATCH. -/
theorem U3Identification.excluded
    {N : LibraryNumericalData} {S : StageOneNumericalData}
    {U : U3RealizationData S} {M : U3KnownModelData}
    (hI : U3Identification N S U M) {r : U3ReportRow} (hr : r ∈ u3ReportP16)
    {n : KnownFiveName}
    (he : (n.sourceName, U3EmbeddingVerdict.no) ∈ r.embedding ∨
      (n.sourceName, U3EmbeddingVerdict.noCount) ∈ r.embedding)
    {X : U3StarData} (hX : U3GeometricStar N S (U.rowClass r).val X)
    (hR : X.radius ∈ radiusClassRegion S (U.rowClass r))
    (hE : U.canonicalEncoding X = U.rowEncoding r) : ¬ U3MatchesKnown N M n X := by
  rcases he with he | he
  · exact hI.soundNO r hr n he X hX hR hE
  · exact hI.soundNOCOUNT r hr n he X hX hR hE

/-- Literal name interpretation plus the explicit external construction
property implies membership in the already concrete families K1--K3. -/
theorem U3Identification.admitted_known
    {N : LibraryNumericalData} {S : StageOneNumericalData}
    {U : U3RealizationData S} {M : U3KnownModelData}
    (hI : U3Identification N S U M) {r : U3ReportRow} (hr : r ∈ u3ReportP16)
    {n : KnownFiveName} (hn : n.sourceName ∈ r.known_names) : Known (M.model n) := by
  obtain ⟨hm, hQ, _⟩ := hI.admitted r hr n hn
  exact knownFiveModel_known hQ hm

/-- Identification by elimination: when the listed model's own star is
represented by a row of this class, every row other than the selected one
is impossible. The finite exclusion pattern is proved from the report. -/
theorem U3Identification.identified_row
    {N : LibraryNumericalData} {S : StageOneNumericalData}
    {T : StageTwoNumericalData S} {U : U3RealizationData S} {M : U3KnownModelData}
    (hI : U3Identification N S U M) (hU : U3Realizations N S T U)
    {r s : U3ReportRow} (hr : r ∈ u3ReportP16) (hs : s ∈ u3ReportP16)
    {n : KnownFiveName} (hn : n.sourceName ∈ r.known_names)
    (hc : U.rowClass r = U.rowClass s)
    {Y : U3StarData} (hY : U3GeometricStar N S (U.rowClass s).val Y)
    (hR : Y.radius ∈ radiusClassRegion S (U.rowClass s))
    (hE : U.canonicalEncoding Y = U.rowEncoding s)
    (hmatch : U3MatchesKnown N M n Y) : s = r := by
  by_contra hne
  have hci := hU.class_indices r hr s hs hc
  have hex := u3ReportP16_other_excluded hr hs hci (Ne.symm hne) hn
  exact hI.excluded hs hex hY hR hE hmatch

end Uniform5.Composition
