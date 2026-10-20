import Uniform5.CompositionRelativeFaces
import Uniform5.Congruence

/-! The actual ridge and an intrinsic facet center span that facet. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- In codimension one, adding any point outside the smaller affine span
exhausts the larger affine span. -/
theorem affineSpan_insert_eq_of_dimension_gap {S T : Set E}
    (hST : S ⊆ T) (hne : S.Nonempty) (hd : affineDimension S + 1 = affineDimension T)
    {a : E} (ha : a ∈ T) (haS : a ∉ affineSpan ℝ S) :
    affineSpan ℝ (insert a S) = affineSpan ℝ T := by
  have hle : affineSpan ℝ (insert a S) ≤ affineSpan ℝ T :=
    affineSpan_mono ℝ (Set.insert_subset ha hST)
  have hlt : affineSpan ℝ S < affineSpan ℝ (insert a S) := by
    apply lt_of_le_of_ne (affineSpan_mono ℝ (Set.subset_insert a S))
    intro hh
    apply haS
    rw [hh]
    exact subset_affineSpan ℝ _ (Set.mem_insert a S)
  have hdl := Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty hlt (hne.mono (subset_affineSpan ℝ S)))
  have hdu := Submodule.finrank_mono (AffineSubspace.direction_le hle)
  have hdeq : (affineSpan ℝ (insert a S)).direction = (affineSpan ℝ T).direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
      (by unfold affineDimension Uniform5.affineDimension at hd; omega)
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdeq
    ⟨a, subset_affineSpan ℝ _ (Set.mem_insert a S)⟩ hle

/-- A ridge and any relative interior point of an incident facet affinely
span the entire facet. No nondegeneracy or spanning premise is supplied. -/
theorem ridge_centre_affineSpan {P F R : Set E} (hF : Facet P F)
    (hR : IsConvexFace P R) (hne : R.Nonempty) (hRF : R ⊆ F)
    (hd : affineDimension R + 2 = affineDimension P) {a : E}
    (ha : a ∈ intrinsicInterior ℝ F) :
    affineSpan ℝ (insert a R) = affineSpan ℝ F := by
  have hRFface := face_restrict hR hF.1.2.1 hRF
  have hproper : R ≠ F := by
    intro hh
    have hdim := hF.2.2
    rw [hh] at hd
    omega
  have hanot : a ∉ affineSpan ℝ R := by
    intro hh
    apply intrinsicInterior_not_mem_proper_face hRFface hproper ha
    rw [← face_affineSpan_inter hRFface hne]
    exact ⟨intrinsicInterior_subset ha, hh⟩
  exact affineSpan_insert_eq_of_dimension_gap hRF hne
    (by have hh := hF.2.2; omega) (intrinsicInterior_subset ha) hanot

/-- The actual ridge vertices suffice: no extra points in the ridge are
needed to recover the facet's affine span. -/
theorem ridge_vertices_centre_affineSpan {P F R : Set E} (hP : FinitePolytope P)
    (hF : Facet P F) (hR : IsConvexFace P R) (hne : R.Nonempty) (hRF : R ⊆ F)
    (hd : affineDimension R + 2 = affineDimension P) {a : E}
    (ha : a ∈ intrinsicInterior ℝ F) :
    affineSpan ℝ (insert a (R.extremePoints ℝ)) = affineSpan ℝ F := by
  have hspan : affineSpan ℝ (R.extremePoints ℝ) = affineSpan ℝ R := by
    rw [← affineSpan_convexHull (𝕜 := ℝ),
      ← finitePolytope_eq_convexHull_extremePoints (finitePolytope_face hP hR hne)]
  rw [← affineSpan_insert_affineSpan, hspan, affineSpan_insert_affineSpan]
  exact ridge_centre_affineSpan hF hR hne hRF hd ha

/-- The precise linear-span premise of `congruence_across_ridge`, derived
from actual ridge incidence and relative interior of the facet center. -/
theorem actual_ridge_centre_spans {P F R : Set E} (hP : FinitePolytope P)
    (hF : Facet P F) (hR : IsConvexFace P R) (hne : R.Nonempty) (hRF : R ⊆ F)
    (hd : affineDimension R + 2 = affineDimension P) {a : E}
    (ha : a ∈ intrinsicInterior ℝ F) {x : E} (hx : x ∈ F) :
    x - a ∈ Submodule.span ℝ ((fun p => p - a) '' R.extremePoints ℝ) := by
  apply ridge_centre_span_of_affineSpan
  rw [ridge_vertices_centre_affineSpan hP hF hR hne hRF hd ha]
  exact subset_affineSpan ℝ F hx

end Uniform5.Composition
