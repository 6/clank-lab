import Uniform5.CompositionU3RealizationInputs

/-! Section U3 step 4: finite retained candidates and exact encodings.
The computation checks encodings of candidates; the resulting local
forcing implication is a theorem, not a field of the input. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Internal candidate lists and anchored encodings. These are distinct
from the diagnostic counts serialized by `locuniq.check`. -/
structure U3ForcingData where
  candidates : U3StarData → Space 5 → List (Space 5 ≃ᵃⁱ[ℝ] Space 5)
  encoding : U3StarData → Space 5 → (Space 5 ≃ᵃⁱ[ℝ] Space 5) → U3Encoding

/-- The centered candidates considered by the independent checker. The
center restriction is essential: `locuniq.frame5` fixes the common center. -/
def u3CenteredCandidates (N : LibraryNumericalData) (X : U3StarData) (w : Space 5) :
    Set (Space 5 ≃ᵃⁱ[ℝ] Space 5) :=
  {g ∈ neighborStarCandidates X.root w (X.star N) | g X.center = X.center}

/-- One forcing check has a complete retained list, a unique anchored
encoding, and sound exact decoding. False interval exclusions are ruled
out by `complete`; interval overlap is never interpreted as equality. -/
structure U3ForcingCheck (N : LibraryNumericalData) (D : U3ForcingData)
    (X : U3StarData) (w : Space 5) : Prop where
  complete : ∀ g ∈ u3CenteredCandidates N X w, g ∈ D.candidates X w
  retained_nonempty : D.candidates X w ≠ []
  encoding_unique : ∀ g ∈ D.candidates X w, ∀ h ∈ D.candidates X w,
    D.encoding X w g = D.encoding X w h
  encoding_sound : ∀ g ∈ D.candidates X w, ∀ h ∈ D.candidates X w,
    D.encoding X w g = D.encoding X w h →
      facetSetImage g (X.star N) = facetSetImage h (X.star N)

/-- Named U3 local-uniqueness computation for every reported realization.
The report's `forced` flag is connected to the exact candidate check.
All 629 flags being true is separately proved by finite reduction. -/
structure U3Forcing (N : LibraryNumericalData) (S : StageOneNumericalData)
    (U : U3RealizationData S) (D : U3ForcingData) : Prop where
  checked : ∀ r ∈ u3ReportP16, r.local_uniqueness.forced = true →
    ∀ X, U3GeometricStar N S (U.rowClass r).val X →
      X.radius ∈ radiusClassRegion S (U.rowClass r) →
      U.canonicalEncoding X = U.rowEncoding r →
      ∀ w, starNeighbor X.root w (X.star N) → U3ForcingCheck N D X w

/-- The encoded check implies equality of the actual moved full stars
for any two geometric candidates that fix the center. -/
theorem U3ForcingCheck.candidate_stars_equal
    {N : LibraryNumericalData} {D : U3ForcingData} {X : U3StarData} {w : Space 5}
    (hcheck : U3ForcingCheck N D X w)
    {g h : Space 5 ≃ᵃⁱ[ℝ] Space 5}
    (hg : g ∈ u3CenteredCandidates N X w) (hh : h ∈ u3CenteredCandidates N X w) :
    facetSetImage g (X.star N) = facetSetImage h (X.star N) :=
  hcheck.encoding_sound g (hcheck.complete g hg) h (hcheck.complete h hh)
    (hcheck.encoding_unique g (hcheck.complete g hg) h (hcheck.complete h hh))

/-- The verified report flags discharge the Boolean guard of the named
forcing computation for any represented geometric star. -/
theorem U3Forcing.candidate_stars_equal
    {N : LibraryNumericalData} {S : StageOneNumericalData}
    {U : U3RealizationData S} {D : U3ForcingData}
    (hF : U3Forcing N S U D) {r : U3ReportRow} (hr : r ∈ u3ReportP16)
    {X : U3StarData} (hX : U3GeometricStar N S (U.rowClass r).val X)
    (hR : X.radius ∈ radiusClassRegion S (U.rowClass r))
    (hE : U.canonicalEncoding X = U.rowEncoding r)
    {w : Space 5} (hw : starNeighbor X.root w (X.star N))
    {g h : Space 5 ≃ᵃⁱ[ℝ] Space 5}
    (hg : g ∈ u3CenteredCandidates N X w) (hh : h ∈ u3CenteredCandidates N X w) :
    facetSetImage g (X.star N) = facetSetImage h (X.star N) :=
  (hF.checked r hr (u3ReportP16_mem_forced hr) X hX hR hE w hw).candidate_stars_equal hg hh

end Uniform5.Composition
