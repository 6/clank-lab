import Uniform5.CompositionIntrinsicModel
import Mathlib.Analysis.Convex.Intrinsic

/-!
# Centered intrinsic coordinate models

A finite polytope can be realized in its exact affine dimension with any
chosen relative-interior point at the origin. Full span and the origin's
relative-interior membership are conclusions of the construction.
-/

noncomputable section
namespace Uniform5.Composition
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonempty subset of Euclidean `n`-space having affine dimension `n`
spans that entire affine space. -/
theorem affineSpan_eq_top_of_dimension {n : ℕ} {Q : Set (Space n)}
    (hne : Q.Nonempty) (hd : affineDimension Q = n) : affineSpan ℝ Q = ⊤ := by
  have hdir : (affineSpan ℝ Q).direction = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [finrank_euclideanSpace_fin] using hd
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ?_).mp hdir
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, subset_affineSpan ℝ Q hx⟩

/-- Any specified relative-interior point becomes the origin in an actual
full-dimensional intrinsic model, with an affine isometry onto the original
polytope. No extra geometric assumption is needed for this normalization. -/
theorem exists_finitePolytope_centered_intrinsic_model [FiniteDimensional ℝ E]
    (P : Set E) (hP : FinitePolytope P) (n : ℕ) (hd : affineDimension P = n)
    (c : E) (hc : c ∈ intrinsicInterior ℝ P) :
    ∃ (f : Space n →ᵃⁱ[ℝ] E) (Q : Set (Space n)),
      f '' Q = P ∧ f 0 = c ∧ FinitePolytope Q ∧ affineDimension Q = n ∧
      (0 : Space n) ∈ intrinsicInterior ℝ Q ∧ affineSpan ℝ Q = ⊤ := by
  obtain ⟨f, Q, him, _, hQ, hdQ⟩ := exists_finitePolytope_intrinsic_model P hP n hd
  rw [← him, f.image_intrinsicInterior] at hc
  obtain ⟨u, hu, huc⟩ := hc
  let g := AffineIsometryEquiv.constVAdd ℝ (Space n) (-u)
  have hgu : g u = 0 := by simp [g]
  have hg0 : g.symm 0 = u := by rw [← hgu, g.symm_apply_apply]
  let f' : Space n →ᵃⁱ[ℝ] E := f.comp g.symm.toAffineIsometry
  have hQ' : FinitePolytope (g '' Q) := (finitePolytope_affineIsometry_image_iff g.toAffineIsometry Q).mpr hQ
  have hdQ' : affineDimension (g '' Q) = n := by
    exact (affineDimension_affineIsometry_image g.toAffineIsometry Q).trans hdQ
  refine ⟨f', g '' Q, ?_, ?_, hQ', hdQ', ?_,
    affineSpan_eq_top_of_dimension (finitePolytope_nonempty hQ') hdQ'⟩
  · change (f.comp g.symm.toAffineIsometry) '' (g '' Q) = P
    rw [show (f.comp g.symm.toAffineIsometry) '' (g '' Q) = f '' Q by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, by simp⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨g z, mem_image_of_mem g hz, by simp⟩]
    exact him
  · change f (g.symm 0) = c
    rw [hg0, huc]
  · change (0 : Space n) ∈ intrinsicInterior ℝ (g.toAffineIsometry '' Q)
    rw [g.toAffineIsometry.image_intrinsicInterior]
    exact ⟨u, hu, hgu⟩

end Uniform5.Composition
