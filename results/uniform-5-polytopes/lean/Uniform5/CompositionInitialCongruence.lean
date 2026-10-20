import Uniform5.CompositionCongruence
import Uniform5.Congruence

/-!
# Initial linear congruence from actual metric data

Equal distances and equal distances from the origin determine a Gram matrix.
An isometry of its span extends to the entire finite-dimensional Euclidean
space. Thus the initial facet extension in Lemma D follows from exact facet
correspondence and a common origin-centred circumsphere; no spanning or
extension assumption is needed.
-/

noncomputable section

namespace Uniform5.Composition

open scoped RealInnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An indexed family with the same Gram matrix is carried to the other
family by an ambient orthogonal transformation, even if it does not span. -/
theorem exists_linearIsometryEquiv_of_inner_eq (v w : ι → E)
    (hgram : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) :
    ∃ A : E ≃ₗᵢ[ℝ] E, ∀ i, A (v i) = w i := by
  classical
  let L : LinearMap.range (Finsupp.linearCombination ℝ v) →ₗᵢ[ℝ] E :=
    gramRangeIsometry v w hgram
  let M : E →ₗᵢ[ℝ] E := L.extend
  have hm (i : ι) : M (v i) = w i := by
    have hv : Finsupp.linearCombination ℝ v (Finsupp.single i 1) = v i := by simp
    have hw : Finsupp.linearCombination ℝ w (Finsupp.single i 1) = w i := by simp
    have hv' : v i ∈ LinearMap.range (Finsupp.linearCombination ℝ v) :=
      ⟨Finsupp.single i 1, hv⟩
    calc
      M (v i) = L ⟨v i, hv'⟩ := L.extend_apply ⟨v i, hv'⟩
      _ = w i := by
        simpa only [hv, hw] using gramRangeIsometry_apply v w hgram (Finsupp.single i 1)
  exact ⟨LinearIsometryEquiv.ofSurjective M
    ((LinearMap.injective_iff_surjective (f := M.toLinearMap)).mp M.injective), hm⟩

/-- Pairwise distances and distances from the origin suffice for an ambient
linear isometric extension. The index set need not be finite or nonempty. -/
theorem exists_linearIsometryEquiv_of_dist_norm_eq (v w : ι → E)
    (hdist : ∀ i j, dist (v i) (v j) = dist (w i) (w j))
    (hnorm : ∀ i, ‖v i‖ = ‖w i‖) :
    ∃ A : E ≃ₗᵢ[ℝ] E, ∀ i, A (v i) = w i := by
  apply exists_linearIsometryEquiv_of_inner_eq
  intro i j
  simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    ← dist_eq_norm, hnorm, hdist]

end Uniform5.Composition

namespace Uniform5.ExactFacetCorrespondence

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {V V' : I → E} {S : Set I} {c c' : E}

omit [FiniteDimensional ℝ E] in
/-- Exact facet correspondence preserves every pairwise labelled distance. -/
theorem pairwise_dist_eq (D : ExactFacetCorrespondence V V' S c c')
    {i j : I} (hi : i ∈ S) (hj : j ∈ S) :
    dist (V i) (V j) = dist (V' i) (V' j) := by
  rw [← D.comparison_points i hi, ← D.comparison_points j hj]
  exact (D.comparison.isometry.dist_eq _ _).symm

/-- Lemma D's initial linear extension is a theorem once the corresponding
facet vertices have equal norms; it is not an extra geometric hypothesis. -/
theorem initial_facet_linear_extension_of_norm_eq
    (D : ExactFacetCorrespondence V V' S c c')
    (hnorm : ∀ i ∈ S, ‖V i‖ = ‖V' i‖) :
    ∃ A : E ≃ₗᵢ[ℝ] E, ∀ i ∈ S, A (V i) = V' i := by
  exact D.initial_linear_extension (fun i hi => (hnorm i hi).symm)

/-- A common origin-centred sphere supplies the equal norms required by the
initial extension, directly from its geometric distance formulation. -/
theorem initial_facet_linear_extension
    (D : ExactFacetCorrespondence V V' S c c') (R : ℝ)
    (hsource : ∀ i ∈ S, dist (V i) 0 = R)
    (htarget : ∀ i ∈ S, dist (V' i) 0 = R) :
    ∃ A : E ≃ₗᵢ[ℝ] E, ∀ i ∈ S, A (V i) = V' i := by
  apply D.initial_facet_linear_extension_of_norm_eq
  intro i hi
  simpa only [dist_zero_right] using (hsource i hi).trans (htarget i hi).symm

end Uniform5.ExactFacetCorrespondence

namespace Uniform5.Composition

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Lemma D's propagation theorem with its initial extension discharged by
exact metric correspondence and a common origin-centred sphere. -/
theorem congruence_from_cospherical_ridge_correspondences
    {F : Type*} (V V' : I → E) (facet : F → Set I)
    (centre centre' : F → E) (adjacent : F → F → Prop)
    (ridge : F → F → Set I)
    (data : ∀ f, ExactFacetCorrespondence V V' (facet f) (centre f) (centre' f))
    (root : F) (R : ℝ)
    (source_sphere : ∀ i ∈ facet root, dist (V i) 0 = R)
    (target_sphere : ∀ i ∈ facet root, dist (V' i) 0 = R)
    (facet_graph_connected : ∀ f, Relation.ReflTransGen adjacent root f)
    (facet_covers : ∀ i, ∃ f, i ∈ facet f)
    (ridge_in_facets : ∀ f g, adjacent f g → ridge f g ⊆ facet f ∩ facet g)
    (ridge_centre_spans : ∀ f g, adjacent f g → ∀ i ∈ facet g,
      V i - centre g ∈ Submodule.span ℝ ((fun j => V j - centre g) '' ridge f g))
    (opposite_side_tangent_centre_unique :
      ∀ (A : E ≃ₗᵢ[ℝ] E) f g, adjacent f g →
        (∀ i ∈ facet f, A (V i) = V' i) → A (centre g) = centre' g) :
    ∃ A : E ≃ₗᵢ[ℝ] E, ∀ i, A (V i) = V' i := by
  exact congruence_from_ridge_correspondences V V' facet centre centre' adjacent ridge
    data root ((data root).initial_facet_linear_extension R source_sphere target_sphere)
    facet_graph_connected facet_covers ridge_in_facets ridge_centre_spans
    opposite_side_tangent_centre_unique

end Uniform5.Composition
