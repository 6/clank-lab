import Uniform5.CompositionEmbedding
import Uniform5.CompositionPolygonSpan

/-!
# Reflection of uniformity through Euclidean embeddings

The reverse regular-polygon case uses the proved full-plane span of the
explicit circular polygon. An adjoint supplies an affine retraction to the
source space, and its restriction to the polygon's entire parametrizing
plane is an isometry. Thus no span or symmetry extension is assumed.
-/

noncomputable section
namespace Uniform5.Composition
open Set

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The adjoint gives an actual affine retraction of an affine isometric
embedding. It is not asserted to be an isometry away from the image. -/
noncomputable def embeddingRetraction (f : E →ᵃⁱ[ℝ] F) : F →ᵃ[ℝ] E := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : CompleteSpace F := FiniteDimensional.complete ℝ F
  exact f.linearIsometry.toContinuousLinearMap.adjoint.toLinearMap.toAffineMap.comp
    (AffineEquiv.constVAdd ℝ F (-f 0)).toAffineMap

@[simp] theorem embeddingRetraction_apply_image (f : E →ᵃⁱ[ℝ] F) (x : E) :
    embeddingRetraction f (f x) = x := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : CompleteSpace F := FiniteDimensional.complete ℝ F
  let T := f.linearIsometry.toContinuousLinearMap
  have hinv : T.adjoint (T x) = x := by
    have hh := T.norm_map_iff_adjoint_comp_self.mp f.linearIsometry.norm_map
    exact congrArg (fun k : E →L[ℝ] E => k x) hh
  have hf : f x = T x + f 0 := by simpa using f.map_vadd 0 x
  change T.adjoint (-f 0 + f x) = x
  rw [hf, show -f 0 + (T x + f 0) = T x by abel]
  exact hinv

theorem embeddingRetraction_right_inverse (f : E →ᵃⁱ[ℝ] F) {y : F}
    (hy : y ∈ Set.range f) : f (embeddingRetraction f y) = y := by
  obtain ⟨x, rfl⟩ := hy
  rw [embeddingRetraction_apply_image]

/-- An affine isometry whose image lies in another embedding's image lifts
to an affine isometry of its source. -/
theorem embedding_lift_affineIsometry (f : E →ᵃⁱ[ℝ] F) (g : G →ᵃⁱ[ℝ] F)
    (h : Set.range g ⊆ Set.range f) :
    ∃ q : G →ᵃⁱ[ℝ] E, ∀ x, f (q x) = g x := by
  let q : G →ᵃ[ℝ] E := (embeddingRetraction f).comp g.toAffineMap
  have hq (x : G) : f (q x) = g x :=
    embeddingRetraction_right_inverse f (h (Set.mem_range_self x))
  have hn (x : G) : ‖q.linear x‖ = ‖x‖ := by
    have hlin : q.linear x = q x - q 0 := by
      simpa using q.linearMap_vsub x 0
    calc
      ‖q.linear x‖ = dist (q x) (q 0) := by rw [hlin, dist_eq_norm]
      _ = dist (f (q x)) (f (q 0)) := (f.dist_map _ _).symm
      _ = dist (g x) (g 0) := by rw [hq x, hq 0]
      _ = ‖x‖ := by rw [g.dist_map, dist_zero_right]
  exact ⟨{ q with norm_map := hn }, hq⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- If the image of a full-span set lies in an affine embedding's range,
then its entire affine parametrization lies in that range. -/
theorem embedding_range_subset_of_span (f : E →ᵃⁱ[ℝ] F) (g : G →ᵃⁱ[ℝ] F)
    (S : Set G) (hs : affineSpan ℝ S = ⊤) (h : g '' S ⊆ Set.range f) :
    Set.range g ⊆ Set.range f := by
  let R : AffineSubspace ℝ F := (⊤ : AffineSubspace ℝ E).map f.toAffineMap
  have hsub : g.toAffineMap '' S ⊆ (R : Set F) := by
    intro x hx
    obtain ⟨y, hy⟩ := h hx
    exact ⟨y, Set.mem_univ y, hy⟩
  have hspan : affineSpan ℝ (g.toAffineMap '' S) ≤ R :=
    affineSpan_le.mpr hsub
  rw [← AffineSubspace.map_span, hs] at hspan
  rintro x ⟨y, rfl⟩
  obtain ⟨z, _, hz⟩ := hspan (show g y ∈ (⊤ : AffineSubspace ℝ G).map g.toAffineMap from
    ⟨y, Set.mem_univ y, rfl⟩)
  exact ⟨z, hz⟩

/-- The regular polygon base case reflects through an affine embedding:
full affine span ensures that its entire plane parametrization lifts. -/
theorem embedding_uniform_two_reflect (f : E →ᵃⁱ[ℝ] F) {P : Set E}
    (h : Uniform 2 (f '' P)) : Uniform 2 P := by
  rw [Uniform] at h ⊢
  obtain ⟨k, hk, r, hr, g, heq⟩ := h
  have hsub : g '' polygon k r ⊆ Set.range f := by
    rw [← heq]
    exact Set.image_subset_range _ _
  obtain ⟨q, hq⟩ := embedding_lift_affineIsometry f g
    (embedding_range_subset_of_span f g (polygon k r)
      (affineSpan_polygon_eq_top k r hk hr) hsub)
  refine ⟨k, hk, r, hr, q, f.injective.image_injective ?_⟩
  rw [heq, Set.image_image]
  exact Set.image_congr (fun x _ => (hq x).symm)

/-- Recursive geometric uniformity reflects through an affine isometric
embedding, including its regular-polygon base case. -/
theorem embedding_uniform_reflect (f : E →ᵃⁱ[ℝ] F) {n : ℕ} {P : Set E}
    (h : Uniform n (f '' P)) : Uniform n P := by
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    rcases n with _ | n
    · rw [Uniform] at h ⊢
      obtain ⟨y, heq⟩ := h
      have hy : y ∈ f '' P := by rw [heq]; exact Set.mem_singleton y
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨x, f.injective.image_injective ?_⟩
      rwa [Set.image_singleton]
    rcases n with _ | n
    · rw [Uniform] at h ⊢
      obtain ⟨y, z, hyz, heq⟩ := h
      have hy : y ∈ f '' P := by rw [heq]; exact left_mem_segment ℝ y z
      have hz : z ∈ f '' P := by rw [heq]; exact right_mem_segment ℝ y z
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      refine ⟨a, b, fun hab => hyz (congrArg f hab), f.injective.image_injective ?_⟩
      have him : f '' segment ℝ a b = segment ℝ (f a) (f b) :=
        image_segment ℝ f.toAffineMap a b
      rwa [him]
    rcases n with _ | n
    · exact embedding_uniform_two_reflect f h
    rw [Uniform] at h ⊢
    refine ⟨(finitePolytope_affineIsometry_image_iff f P).mp h.1, ?_,
      embedding_vertexTransitive_preimage f h.2.2.1, ?_⟩
    · rw [← affineDimension_affineIsometry_image f P]
      exact h.2.1
    · intro A hA
      exact ih (n + 2) (by omega) (h.2.2.2 _ (embedding_facet_image f hA))

/-- Uniformity is an intrinsic Euclidean property even when its two
realizations occupy ambient spaces of different dimensions. -/
theorem embedding_uniform_iff (f : E →ᵃⁱ[ℝ] F) (n : ℕ) (P : Set E) :
    Uniform n (f '' P) ↔ Uniform n P :=
  ⟨embedding_uniform_reflect f, embedding_uniform_image f⟩

theorem embedding_unitUniform_reflect (f : E →ᵃⁱ[ℝ] F) {n : ℕ} {P : Set E}
    (h : UnitUniform n (f '' P)) : UnitUniform n P :=
  ⟨embedding_uniform_reflect f h.1, embedding_unitEdges_reflect f h.2⟩

theorem embedding_unitUniform_iff (f : E →ᵃⁱ[ℝ] F) (n : ℕ) (P : Set E) :
    UnitUniform n (f '' P) ↔ UnitUniform n P :=
  ⟨embedding_unitUniform_reflect f, embedding_unitUniform_image f⟩

omit [FiniteDimensional ℝ F] in
/-- A unit uniform polytope in dimension at least three has a genuinely
unit uniform full-dimensional Euclidean coordinate model. -/
theorem exists_unitUniform_intrinsic_model {P : Set E} {n : ℕ}
    (hP : UnitUniform (n + 3) P) :
    ∃ (f : Space (n + 3) →ᵃⁱ[ℝ] E) (Q : Set (Space (n + 3))),
      f '' Q = P ∧ Congruent Q P ∧ UnitUniform (n + 3) Q := by
  obtain ⟨f, Q, him, hc, _, _⟩ := exists_finitePolytope_intrinsic_model P
    (uniform_finitePolytope hP.1) (n + 3) (uniform_dimension hP.1)
  refine ⟨f, Q, him, hc, embedding_unitUniform_reflect f ?_⟩
  rwa [him]

end Uniform5.Composition
