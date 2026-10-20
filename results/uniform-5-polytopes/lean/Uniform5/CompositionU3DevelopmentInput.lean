import Uniform5.CompositionU3RealizationInputs
import Uniform5.CompositionCenteredStars
import Uniform5.CompositionRootInput
import Uniform5.CompositionU3StarCongruence

/-! DEV refutes hypothetical actual stars represented by the extra row of
the independent report. It does not assert that a retained interval state
has an exact realization. The facet multiset alone would also describe a
known simplex construction and is insufficient to identify the row. -/
noncomputable section
namespace Uniform5.Composition
open Set
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The report's extra realization: class 18, signature 0, realization 0.
Its position in the flattened serialized list is twelve. -/
noncomputable def u3RefutedRow : U3ReportRow :=
  u3ReportP16.get ⟨12, by rw [u3ReportP16_length]; decide⟩

theorem u3RefutedRow_index : u3RefutedRow.index = (18, 0, 0) := by decide

theorem u3RefutedRow_verdict : u3RefutedRow.verdict = .refuted := by decide

theorem u3RefutedRow_mem : u3RefutedRow ∈ u3ReportP16 :=
  List.get_mem _ _

theorem u3ReportP16_refuted_unique {r : U3ReportRow}
    (hr : r ∈ u3ReportP16) (hv : r.verdict = .refuted) : r = u3RefutedRow := by
  have hall : u3ReportP16.all (fun s =>
      !(s.verdict == .refuted) || s == u3RefutedRow) = true := by decide
  simpa [hv] using List.all_eq_true.mp hall r hr

/-- The named DEV input: no convex unit-uniform five-polytope has the
full actual star represented by the refuted row.
Geometry, radius-class membership, closure and canonical encoding guard
the refutation. The root, centre and entire incident facet set must be
those of the same polytope; unlabelled figure congruence is insufficient.
No exact reference star is assumed to exist. The unused
`extra` parameter preserves the paper-facing theorem interface. Search
coverage is absent here and belongs to U3Realizations. -/
structure DEV (N : LibraryNumericalData) (S : StageOneNumericalData)
    (U : U3RealizationData S) (extra : U3StarData) : Prop where
  refutation : ∀ X, U3GeometricStar N S (U.rowClass u3RefutedRow).val X →
    X.radius ∈ radiusClassRegion S (U.rowClass u3RefutedRow) →
    (U.rowSignature u3RefutedRow).RadiusCompatible N X.radius →
    U.canonicalEncoding X = U.rowEncoding u3RefutedRow →
    ∀ P : UnitUniform5, ∀ v ∈ P.val.extremePoints ℝ,
      X.root = v → X.center = polytopeCenter P →
      X.star N = facetStar P.val v → False

/-- Refutation applies to the full actual star, with its root and centre,
without any test of membership in the known families. -/
theorem DEV.no_polytope_with_extra_star
    {N : LibraryNumericalData} {S : StageOneNumericalData}
    {U : U3RealizationData S} {extra : U3StarData} (h : DEV N S U extra)
    (hX : U3GeometricStar N S (U.rowClass u3RefutedRow).val extra)
    (hR : extra.radius ∈ radiusClassRegion S (U.rowClass u3RefutedRow))
    (hC : (U.rowSignature u3RefutedRow).RadiusCompatible N extra.radius)
    (hE : U.canonicalEncoding extra = U.rowEncoding u3RefutedRow)
    (P : UnitUniform5) {v : Space 5} (hv : v ∈ P.val.extremePoints ℝ)
    (hroot : extra.root = v) (hcenter : extra.center = polytopeCenter P)
    (hstar : extra.star N = facetStar P.val v) : False :=
  h.refutation extra hX hR hC hE P v hv hroot hcenter hstar

/-- If an exact reference star is supplied separately, ROOT supplies the
radius equality needed for encoding rigidity. DEV does not provide the
reference star's existence or these geometric premises. -/
theorem DEV.refuted_row_congruent
    {N : LibraryNumericalData} {S : StageOneNumericalData}
    {T : StageTwoNumericalData S} {U : U3RealizationData S}
    {extra X : U3StarData} (hD : DEV N S U extra)
    (hU : U3Realizations N S T U) (hROOT : ROOT N S T)
    (hX : U3GeometricStar N S (U.rowClass u3RefutedRow).val X)
    (hR : X.radius ∈ radiusClassRegion S (U.rowClass u3RefutedRow))
    (hC : (U.rowSignature u3RefutedRow).RadiusCompatible N X.radius)
    (hE : U.canonicalEncoding X = U.rowEncoding u3RefutedRow)
    (hExtra : U3GeometricStar N S (U.rowClass u3RefutedRow).val extra)
    (hExtraR : extra.radius ∈ radiusClassRegion S (U.rowClass u3RefutedRow))
    (hExtraC : (U.rowSignature u3RefutedRow).RadiusCompatible N extra.radius)
    (hExtraE : U.canonicalEncoding extra = U.rowEncoding u3RefutedRow) :
    U3StarCongruent N X extra := by
  have hr := u3RefutedRow_mem
  have he : X.radius = extra.radius := hROOT.radius_unique (U.rowClass u3RefutedRow)
    (hU.class_valid _ hr) (hU.signature_valid _ hr) hR hExtraR hC hExtraC
  exact hU.same_row_congruent hr hX hExtra hR hExtraR he hE hExtraE

/-- A genuine full actual star following the refuted row is
impossible directly by DEV. The realization and ROOT parameters remain
for interface compatibility; no reference realization is required. -/
theorem DEV.refuted_row_impossible
    {N : LibraryNumericalData} {S : StageOneNumericalData}
    {T : StageTwoNumericalData S} {U : U3RealizationData S}
    {extra X : U3StarData} (hD : DEV N S U extra)
    (hU : U3Realizations N S T U) (hROOT : ROOT N S T)
    (hX : U3GeometricStar N S (U.rowClass u3RefutedRow).val X)
    (hR : X.radius ∈ radiusClassRegion S (U.rowClass u3RefutedRow))
    (hC : (U.rowSignature u3RefutedRow).RadiusCompatible N X.radius)
    (hE : U.canonicalEncoding X = U.rowEncoding u3RefutedRow)
    (P : UnitUniform5) {v : Space 5} (hv : v ∈ P.val.extremePoints ℝ)
    (hroot : X.root = v) (hcenter : X.center = polytopeCenter P)
    (hstar : X.star N = facetStar P.val v) : False :=
  hD.refutation X hX hR hC hE P v hv hroot hcenter hstar

end Uniform5.Composition
