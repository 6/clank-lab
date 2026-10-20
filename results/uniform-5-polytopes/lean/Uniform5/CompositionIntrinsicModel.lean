import Uniform5.CompositionCongruence

/-!
# Euclidean coordinate models of intrinsic dimension

An actual nonempty hull of affine dimension `n` admits an affine-isometric
coordinate realization in `Space n`. The model is the inverse image of the
original set under an explicit affine-span parametrization; no classification
or uniformity conclusion is included in this construction.
-/

noncomputable section
namespace Uniform5.Composition
open Set

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- An affine isometric embedding identifies a set with its image,
even when the ambient dimensions differ. -/
theorem congruent_affineIsometry_image (f : E →ᵃⁱ[ℝ] F) (P : Set E) :
    Congruent P (f '' P) := by
  refine ⟨{ toEquiv := Equiv.Set.image f P f.injective, isometry_toFun := ?_ }⟩
  intro x y
  exact f.isometry x y

/-- Affine isometric embeddings preserve the actual affine dimension. -/
theorem affineDimension_affineIsometry_image (f : E →ᵃⁱ[ℝ] F) (P : Set E) :
    affineDimension (f '' P) = affineDimension P := by
  unfold affineDimension Uniform5.affineDimension
  change Module.finrank ℝ (affineSpan ℝ (f.toAffineMap '' P)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  exact ((affineSpan ℝ P).direction.equivMapOfInjective
    f.linear f.linearIsometry.injective).finrank_eq.symm

/-- The finite-convex-hull condition is intrinsic under affine isometric
embeddings, including the reverse direction needed for coordinate models. -/
theorem finitePolytope_affineIsometry_image_iff (f : E →ᵃⁱ[ℝ] F) (P : Set E) :
    FinitePolytope (f '' P) ↔ FinitePolytope P := by
  classical
  constructor
  · rintro ⟨V, hV, heq⟩
    have hsub : (V : Set F) ⊆ Set.range f := by
      intro z hz
      have hzc := subset_convexHull ℝ (V : Set F) hz
      rw [← heq] at hzc
      exact ⟨hzc.choose, hzc.choose_spec.2⟩
    have hfinite : (f ⁻¹' (V : Set F)).Finite := V.finite_toSet.preimage f.injective.injOn
    let W : Finset E := hfinite.toFinset
    have hW : (W : Set E) = f ⁻¹' (V : Set F) := hfinite.coe_toFinset
    have him : f '' (W : Set E) = (V : Set F) := by
      rw [hW]
      exact Set.image_preimage_eq_of_subset hsub
    have hWne : W.Nonempty := by
      obtain ⟨z, hz⟩ := hV
      obtain ⟨x, hx⟩ := hsub hz
      refine ⟨x, ?_⟩
      change x ∈ (W : Set E)
      rw [hW]
      simpa [hx] using hz
    refine ⟨W, hWne, f.injective.image_injective ?_⟩
    have hh : f '' convexHull ℝ (W : Set E) =
        convexHull ℝ (f '' (W : Set E)) := f.toAffineMap.image_convexHull _
    rw [hh, him]
    exact heq
  · rintro ⟨V, hV, rfl⟩
    refine ⟨V.image f, hV.image f, ?_⟩
    simpa only [Finset.coe_image] using f.toAffineMap.image_convexHull (V : Set E)

/-- Every nonempty set has an actual Euclidean coordinate realization in
its affine dimension. The image equality is witnessed by an affine isometry. -/
theorem exists_intrinsic_euclidean_model [FiniteDimensional ℝ E]
    (P : Set E) (hP : P.Nonempty) (n : ℕ) (hd : affineDimension P = n) :
    ∃ (f : Space n →ᵃⁱ[ℝ] E) (Q : Set (Space n)), f '' Q = P ∧ Congruent Q P := by
  classical
  obtain ⟨a, ha⟩ := hP
  let S := affineSpan ℝ P
  let a₀ : S := ⟨a, subset_affineSpan ℝ P ha⟩
  letI : Nonempty S := ⟨a₀⟩
  let b : OrthonormalBasis (Fin n) ℝ S.direction :=
    (stdOrthonormalBasis ℝ S.direction).reindex (finCongr hd)
  let e : S ≃ᵃⁱ[ℝ] Space n :=
    (AffineIsometryEquiv.vaddConst ℝ a₀).symm.trans b.repr.toAffineIsometryEquiv
  let f : Space n →ᵃⁱ[ℝ] E := S.subtypeₐᵢ.comp e.symm.toAffineIsometry
  have hsub : P ⊆ Set.range f := by
    intro x hx
    let x₀ : S := ⟨x, subset_affineSpan ℝ P hx⟩
    refine ⟨e x₀, ?_⟩
    change ((e.symm (e x₀) : S) : E) = x
    rw [e.symm_apply_apply]
  have hi : f '' (f ⁻¹' P) = P := Set.image_preimage_eq_of_subset hsub
  refine ⟨f, f ⁻¹' P, hi, ?_⟩
  have hg := congruent_affineIsometry_image f (f ⁻¹' P)
  rw [hi] at hg
  exact hg

/-- A finite polytope of affine dimension `n` has a full-dimensional finite
polytope coordinate model in Euclidean `n`-space. -/
theorem exists_finitePolytope_intrinsic_model [FiniteDimensional ℝ E]
    (P : Set E) (hP : FinitePolytope P) (n : ℕ) (hd : affineDimension P = n) :
    ∃ (f : Space n →ᵃⁱ[ℝ] E) (Q : Set (Space n)),
      f '' Q = P ∧ Congruent Q P ∧ FinitePolytope Q ∧ affineDimension Q = n := by
  obtain ⟨f, Q, him, hc⟩ :=
    exists_intrinsic_euclidean_model P (finitePolytope_nonempty hP) n hd
  refine ⟨f, Q, him, hc, ?_, ?_⟩
  · apply (finitePolytope_affineIsometry_image_iff f Q).mp
    rwa [him]
  · rw [← affineDimension_affineIsometry_image f Q, him, hd]

end Uniform5.Composition
