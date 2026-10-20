import Uniform5.CompositionCenteredStars
import Uniform5.CompositionU3ForcingInputs
import Uniform5.CompositionKnownTransport

/-! The exact U3 candidate computation implies equality of actual complete
polytopes sharing the centered star, then congruence for congruent stars. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem U3Forcing.global_equal
    {N : LibraryNumericalData} {S : StageOneNumericalData}
    {U : U3RealizationData S} {D : U3ForcingData}
    (hF : U3Forcing N S U D) {r : U3ReportRow} (hr : r ∈ u3ReportP16)
    (hforced : r.local_uniqueness.forced = true)
    {X : U3StarData} (hX : U3GeometricStar N S (U.rowClass r).val X)
    (hR : X.radius ∈ radiusClassRegion S (U.rowClass r))
    (hE : U.canonicalEncoding X = U.rowEncoding r)
    {A B : UnitUniform5}
    (hcA : polytopeCenter A = X.center) (hcB : polytopeCenter B = X.center)
    (hrA : X.root ∈ A.val.extremePoints ℝ) (hrB : X.root ∈ B.val.extremePoints ℝ)
    (hsA : facetStar A.val X.root = X.star N)
    (hsB : facetStar B.val X.root = X.star N) : A = B := by
  have heq : (⟨A, hcA⟩ : CenteredUnitUniform5 X.center) = ⟨B, hcB⟩ := by
    apply centered_neighbor_candidates_global X.center X.root (X.star N) ?_ hrA hrB hsA hsB
    intro w hw g hg hgc h hh hhc
    exact (hF.checked r hr hforced X hX hR hE w hw).candidate_stars_equal
      ⟨hg, hgc⟩ ⟨hh, hhc⟩
  exact congrArg Subtype.val heq

theorem U3Forcing.congruent_of_stars
    {N : LibraryNumericalData} {S : StageOneNumericalData}
    {U : U3RealizationData S} {D : U3ForcingData}
    (hF : U3Forcing N S U D) {r : U3ReportRow} (hr : r ∈ u3ReportP16)
    (hforced : r.local_uniqueness.forced = true)
    {X Y : U3StarData} (hY : U3GeometricStar N S (U.rowClass r).val Y)
    (hR : Y.radius ∈ radiusClassRegion S (U.rowClass r))
    (hE : U.canonicalEncoding Y = U.rowEncoding r)
    {A B : UnitUniform5}
    (hcA : polytopeCenter A = X.center) (hcB : polytopeCenter B = Y.center)
    (hrA : X.root ∈ A.val.extremePoints ℝ) (hrB : Y.root ∈ B.val.extremePoints ℝ)
    (hsA : facetStar A.val X.root = X.star N)
    (hsB : facetStar B.val Y.root = Y.star N)
    (hcon : U3StarCongruent N X Y) : Congruent A.val B.val := by
  obtain ⟨g, hgr, hgc, hgs⟩ := hcon
  have hc : polytopeCenter (A.image g) = Y.center := by
    rw [polytopeCenter_image, hcA, hgc]
  have hv : Y.root ∈ (A.image g).val.extremePoints ℝ := by
    rw [← hgr]
    exact (UnitUniform5.image_mem_vertices g A X.root).mpr hrA
  have hs : facetStar (A.image g).val Y.root = Y.star N := by
    change facetStar (g '' A.val) Y.root = Y.star N
    rw [← hgr, facetStar_image, hsA, hgs]
  have heq := hF.global_equal hr hforced hY hR hE hc hcB hv hrB hs hsB
  have him : g '' A.val = B.val := congrArg Subtype.val heq
  exact him ▸ congruent_affineIsometryEquiv_image g A.val

end Uniform5.Composition
