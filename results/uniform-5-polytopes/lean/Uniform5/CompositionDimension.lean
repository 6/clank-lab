import Uniform5.CompositionGeometry
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dimension of radial sections

A spanning set lying in a nonzero linear functional's level-one hyperplane
has affine codimension one. Radial rescaling by nonzero factors preserves
linear span, so this applies to the genuine convex hull of normalized rays.
-/

noncomputable section
namespace Uniform5.Composition
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Adding the origin converts affine direction span to linear span. -/
theorem vectorSpan_insert_zero_eq_span (S : Set E) :
    vectorSpan ℝ (insert 0 S) = Submodule.span ℝ S := by
  rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_insert 0 S)]
  simp

/-- Directions of a set in a level hyperplane lie in the functional's kernel. -/
theorem vectorSpan_le_ker_of_level (L : E →ₗ[ℝ] ℝ) (S : Set E) (c : ℝ)
    (hlevel : ∀ x ∈ S, L x = c) : vectorSpan ℝ S ≤ LinearMap.ker L := by
  rw [vectorSpan_def]
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, y, hy, rfl⟩
  change L (x - y) = 0
  simp [hlevel x hx, hlevel y hy]

/-- A linearly spanning set in a level-one hyperplane has affine codimension
one. No finiteness or convexity assumption on the set is needed. -/
theorem affineDimension_add_one_eq_of_level_span [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] ℝ) (S : Set E) (hne : S.Nonempty)
    (hlevel : ∀ x ∈ S, L x = 1) (hspan : Submodule.span ℝ S = ⊤) :
    affineDimension S + 1 = Module.finrank ℝ E := by
  obtain ⟨a, ha⟩ := hne
  have hL : L ≠ 0 := by
    intro hz
    have := hlevel a ha
    simp [hz] at this
  have hupper := Submodule.finrank_mono (vectorSpan_le_ker_of_level L S 1 hlevel)
  have hlower := finrank_vectorSpan_insert_le_set ℝ S 0
  rw [vectorSpan_insert_zero_eq_span, hspan, finrank_top] at hlower
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hL
  rw [affineDimension, Uniform5.affineDimension, direction_affineSpan]
  omega

/-- The affine direction of a spanning level-one set is exactly the kernel,
not merely a subspace of the right dimension. -/
theorem direction_eq_ker_of_level_span [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] ℝ) (S : Set E) (hne : S.Nonempty)
    (hlevel : ∀ x ∈ S, L x = 1) (hspan : Submodule.span ℝ S = ⊤) :
    (affineSpan ℝ S).direction = LinearMap.ker L := by
  have hdim := affineDimension_add_one_eq_of_level_span L S hne hlevel hspan
  obtain ⟨a, ha⟩ := hne
  have hL : L ≠ 0 := by
    intro hz
    have := hlevel a ha
    simp [hz] at this
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hL
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [direction_affineSpan]
    exact vectorSpan_le_ker_of_level L S 1 hlevel
  · unfold affineDimension Uniform5.affineDimension at hdim
    omega

/-- The affine span of a spanning level-one set is the entire cutting
hyperplane. -/
theorem affineSpan_eq_level_of_span [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] ℝ) (S : Set E) (hne : S.Nonempty)
    (hlevel : ∀ x ∈ S, L x = 1) (hspan : Submodule.span ℝ S = ⊤) :
    (affineSpan ℝ S : Set E) = {x | L x = 1} := by
  have hdir := direction_eq_ker_of_level_span L S hne hlevel hspan
  obtain ⟨a, ha⟩ := hne
  have ha' : a ∈ affineSpan ℝ S := subset_affineSpan ℝ S ha
  ext x
  have hm := AffineSubspace.vadd_mem_iff_mem_direction (x - a) ha'
  simpa only [vadd_eq_add, sub_add_cancel, hdir, LinearMap.mem_ker, map_sub,
    hlevel a ha, sub_eq_zero, Set.mem_setOf_eq] using hm

/-- Independently rescaling each generator by a nonzero factor does not
change its linear span. -/
theorem span_image_pointwise_smul (S : Set E) (r : E → ℝ)
    (hr : ∀ x ∈ S, r x ≠ 0) :
    Submodule.span ℝ ((fun x => r x • x) '' S) = Submodule.span ℝ S := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨x, hx, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
  · apply Submodule.span_le.mpr
    intro x hx
    have h := Submodule.smul_mem
      (Submodule.span ℝ ((fun x => r x • x) '' S)) (r x)⁻¹
      (Submodule.subset_span (Set.mem_image_of_mem (fun x => r x • x) hx))
    simpa [smul_smul, hr x hx] using h

/-- The convex hull of normalized rays has exactly one dimension less than
the ambient space whenever the original rays span it. -/
theorem affineDimension_radialHull_add_one [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] ℝ) (S : Set E) (hne : S.Nonempty)
    (hL : ∀ x ∈ S, L x ≠ 0) (hspan : Submodule.span ℝ S = ⊤) :
    affineDimension (convexHull ℝ ((fun x => (L x)⁻¹ • x) '' S)) + 1 =
      Module.finrank ℝ E := by
  have hsp : Submodule.span ℝ ((fun x => (L x)⁻¹ • x) '' S) = ⊤ := by
    rw [span_image_pointwise_smul S (fun x => (L x)⁻¹)
      (fun x hx => inv_ne_zero (hL x hx)), hspan]
  have hlev : ∀ y ∈ ((fun x => (L x)⁻¹ • x) '' S), L y = 1 := by
    rintro y ⟨x, hx, rfl⟩
    simp [hL x hx]
  have hd := affineDimension_add_one_eq_of_level_span L _ (hne.image _) hlev hsp
  unfold affineDimension Uniform5.affineDimension at *
  rw [affineSpan_convexHull (𝕜 := ℝ)]
  exact hd

/-- The vectors along all rays from a generator span the affine direction
space of the original generator set. The apex itself can be omitted. -/
theorem span_vertex_differences_eq_direction (S : Set E) {v : E} (hv : v ∈ S) :
    Submodule.span ℝ ((fun x => x - v) '' (S \ {v})) =
      (affineSpan ℝ S).direction := by
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right_ne ℝ hv]
  rfl

/-- At a zero apex, deleting the apex converts affine direction to the
ordinary linear span of the remaining generators. -/
theorem direction_finiteHull_zero [DecidableEq E] (V : Finset E) (hzero : 0 ∈ V) :
    (affineSpan ℝ (convexHull ℝ (V : Set E))).direction =
      Submodule.span ℝ (V.erase 0 : Set E) := by
  rw [affineSpan_convexHull (𝕜 := ℝ), direction_affineSpan,
    vectorSpan_eq_span_vsub_finset_right_ne ℝ hzero]
  simp

/-- For a full-dimensional finite hull with zero as a generator, its radial
section hull has codimension one. Nonemptiness of the deleted generator set
and its spanning property are conclusions of the original dimension bound. -/
theorem finiteHull_radialHull_dimension [FiniteDimensional ℝ E] [DecidableEq E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →ₗ[ℝ] ℝ)
    (hL : ∀ x ∈ V.erase 0, L x ≠ 0)
    (hfull : affineDimension (convexHull ℝ (V : Set E)) = Module.finrank ℝ E)
    (hpos : 0 < Module.finrank ℝ E) :
    affineDimension (convexHull ℝ ((fun x => (L x)⁻¹ • x) '' (V.erase 0 : Set E))) + 1 =
      Module.finrank ℝ E := by
  have hd : Module.finrank ℝ (Submodule.span ℝ (V.erase 0 : Set E)) =
      Module.finrank ℝ E := by
    unfold affineDimension Uniform5.affineDimension at hfull
    rw [direction_finiteHull_zero V hzero] at hfull
    exact hfull
  have hspan : Submodule.span ℝ (V.erase 0 : Set E) = ⊤ :=
    Submodule.eq_top_of_finrank_eq hd
  have hne : (V.erase 0 : Set E).Nonempty := by
    by_contra hn
    have hempty : (V.erase 0 : Set E) = ∅ := by
      exact Set.not_nonempty_iff_eq_empty.mp hn
    rw [hempty, Submodule.span_empty, finrank_bot] at hd
    omega
  exact affineDimension_radialHull_add_one L _ hne hL hspan

end Uniform5.Composition
