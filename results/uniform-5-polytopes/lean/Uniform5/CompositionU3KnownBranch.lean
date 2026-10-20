import Uniform5.CompositionActualU3Star
import Uniform5.CompositionU3GlobalForcing
import Uniform5.CompositionU3IdentificationInputs
import Uniform5.CompositionU3KnownNamesP16
import Uniform5.CompositionU3ReportGroupsP16
import Uniform5.CompositionRootRegionCoverage
import Uniform5.CompositionCaseBTypeIIIRadius

/-! Actual known-row identification by exclusion, ROOT, and centered
forcing. The known construction's small-face property is derived using B2. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_smallFaces_of_radius_mem
    (classification4D : CitedClassification4D)
    {S : StageOneNumericalData} (hB2 : CaseB.B2 (stageOneOmega S))
    {P : Set (Space 5)} (hP : UnitUniform 5 P)
    {c : ActiveRootClass S} (hR : intrinsicRadius P ∈ radiusClassRegion S c) :
    SmallFaces P := by
  intro F n hn
  by_contra hlarge
  exact unitUniform5_largePolygon_radius_not_mem classification4D hB2 hP hn
    (by omega) (radiusClassRegion_subset_stageOneOmega S c hR)

theorem u3_known_row_classifies
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (T : StageTwoNumericalData S)
    (U : U3RealizationData S) (M : U3KnownModelData) (D : U3ForcingData)
    (hLIB : LIB N) (hS1 : S1 N S) (hS2 : S2 N S T) (hROOT : ROOT N S T)
    (hB2 : CaseB.B2 (stageOneOmega S))
    (hU : U3Realizations N S T U) (hI : U3Identification N S U M)
    (hF : U3Forcing N S U D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P)
    {r : U3ReportRow} (hr : r ∈ u3ReportP16) (hk : r.verdict = .known)
    {X : U3StarData} (hX : U3GeometricStar N S (U.rowClass r).val X)
    (hxv : X.root ∈ P.extremePoints ℝ)
    (hxc : X.center = vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    (hxs : X.star N = facetStar P X.root)
    (hxR : X.radius ∈ radiusClassRegion S (U.rowClass r))
    (hxσ : X.figure.signature hX.figure = U.rowSignature r)
    (hxcl : (X.figure.signature hX.figure).RadiusCompatible N X.radius)
    (hxE : U.canonicalEncoding X = U.rowEncoding r) : Known P := by
  obtain ⟨n, hn⟩ := u3ReportP16_known_named hr hk
  obtain ⟨hm, hQ, hvQ, hcQ, hRQ, _⟩ := hI.admitted r hr n hn
  have hsQ := unitUniform5_smallFaces_of_radius_mem classification4D hB2 hQ hRQ
  obtain ⟨c, hc, Y, hyv, hyc, hyR, hys, hY, hRY, hσY, hclY⟩ :=
    unitUniform5_smallFaces_u3_star classification3D classification4D hQ hsQ hvQ
      N S T hLIB hS1 hS2
  have hc_eq : c = U.rowClass r := radiusClassRegion_eq_of_common_radius S
    (by rwa [hyR] at hRY) hRQ
  subst c
  obtain ⟨s, hs, hsc, hsσ, hsE⟩ := hU.complete (U.rowClass r) hc Y hY hRY hσY
  have hY' : U3GeometricStar N S (U.rowClass s).val Y := hsc.symm ▸ hY
  have hRY' : Y.radius ∈ radiusClassRegion S (U.rowClass s) := hsc.symm ▸ hRY
  have hmatch : U3MatchesKnown N M n Y := by
    refine ⟨AffineIsometryEquiv.refl ℝ (Space 5), hyv, hyc.trans hcQ.symm, ?_⟩
    simpa [facetSetImage, hyv] using hys
  have hrs : r = s := by
    by_contra hne
    have he := u3ReportP16_other_excluded hr hs
      (hU.class_indices r hr s hs hsc.symm) hne hn
    exact hI.excluded hs he hY' hRY' hsE hmatch
  subst s
  have hsig : X.figure.signature hX.figure = Y.figure.signature hY.figure :=
    hxσ.trans hsσ
  have heqR : X.radius = Y.radius := hROOT.radius_unique (U.rowClass r) hc
    (hU.signature_valid r hr) hxR hRY
    (hxσ ▸ hxcl) (hsσ.symm ▸ hclY)
  have hcon := hU.same_row_congruent hr hX hY hxR hRY heqR hxE hsE
  have hpq : Congruent P (M.model n) := hF.congruent_of_stars hr
    (u3ReportP16_mem_forced hr) hY hRY hsE
    (A := ⟨P, hP⟩) (B := ⟨M.model n, hQ⟩)
    hxc.symm hyc.symm hxv (hyv ▸ hvQ) hxs.symm (by simpa [hyv] using hys.symm) hcon
  exact (known_congruent_iff hpq).mpr (knownFiveModel_known hQ hm)

end Uniform5.Composition
