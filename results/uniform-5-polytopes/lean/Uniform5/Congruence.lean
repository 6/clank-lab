import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Relation
import Uniform5.Tangent
import Mathlib.Analysis.InnerProductSpace.Projection

/-!
# Congruence from exact facet correspondences

The algebraic and propagation parts of paper Lemma `lem:D`. Convex-polytope
geometry enters through the explicitly named hypotheses of
`congruence_from_ridge_correspondences`: initial facet extension, opposite-side
tangent-centre uniqueness, ridge-and-centre spanning, and graph connectivity.
In particular no hypothesis assumes agreement on the next facet.
-/

noncomputable section

namespace Uniform5

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact discrete data of one facet. Both placements and the model
symmetry are actual affine isometries; a permutation alone is insufficient.
The source labels cover the facet. The target labels differ by the permutation
realised by the exact symmetry, which fixes the model centre. -/
structure ExactFacetCorrespondence (V V' : I → E) (S : Set I) (c c' : E) where
  Index : Type
  model : Index → E
  sourceLabel : Index → I
  targetLabel : Index → I
  source_covers : ∀ i ∈ S, ∃ t, sourceLabel t = i
  sourcePlacement : E ≃ᵃⁱ[ℝ] E
  targetPlacement : E ≃ᵃⁱ[ℝ] E
  source_points : ∀ t, sourcePlacement (model t) = V (sourceLabel t)
  target_points : ∀ t, targetPlacement (model t) = V' (targetLabel t)
  relabelling : Index ≃ Index
  correspondence : ∀ t, targetLabel t = sourceLabel (relabelling t)
  symmetry : E ≃ᵃⁱ[ℝ] E
  realises : ∀ t, symmetry (model t) = model (relabelling t)
  modelCentre : E
  symmetry_centre : symmetry modelCentre = modelCentre
  source_centre : sourcePlacement modelCentre = c
  target_centre : targetPlacement modelCentre = c'

namespace ExactFacetCorrespondence

variable {V V' : I → E} {S : Set I} {c c' : E}
variable (D : ExactFacetCorrespondence V V' S c c')

/-- The comparison in Lemma D(1) is exactly `g' ε⁻¹ g⁻¹`. -/
def comparison : E ≃ᵃⁱ[ℝ] E :=
  (D.sourcePlacement.symm.trans D.symmetry.symm).trans D.targetPlacement

theorem comparison_points (i : I) (hi : i ∈ S) :
    D.comparison (V i) = V' i := by
  obtain ⟨t, rfl⟩ := D.source_covers i hi
  have he : D.symmetry.symm (D.model t) = D.model (D.relabelling.symm t) := by
    apply D.symmetry.injective
    simp only [AffineIsometryEquiv.apply_symm_apply, D.realises,
      Equiv.apply_symm_apply]
  change D.targetPlacement (D.symmetry.symm (D.sourcePlacement.symm
    (V (D.sourceLabel t)))) = _
  rw [← D.source_points, D.sourcePlacement.symm_apply_apply, he,
    D.target_points, D.correspondence, D.relabelling.apply_symm_apply]

theorem comparison_centre : D.comparison c = c' := by
  have he : D.symmetry.symm D.modelCentre = D.modelCentre := by
    apply D.symmetry.injective
    rw [D.symmetry.apply_symm_apply, D.symmetry_centre]
  change D.targetPlacement (D.symmetry.symm (D.sourcePlacement.symm c)) = c'
  have hs : D.sourcePlacement.symm c = D.modelCentre := by
    apply D.sourcePlacement.injective
    exact (D.sourcePlacement.apply_symm_apply c).trans D.source_centre.symm
  rw [hs, he, D.target_centre]

end ExactFacetCorrespondence

/-- An affine congruence between points at equal distances from the origin
extends on those points to an ambient linear isometry. Reflecting its linear
part in the perpendicular bisector direction corrects its translation. -/
theorem affine_isometry_linear_extension (T : E ≃ᵃⁱ[ℝ] E) (s : Set E)
    (hnorm : ∀ x ∈ s, ‖T x‖ = ‖x‖) :
    ∃ A : E ≃ₗᵢ[ℝ] E, ∀ x ∈ s, A x = T x := by
  let L := T.linearIsometryEquiv
  let K : Submodule ℝ E := ℝ ∙ (-T 0)
  refine ⟨L.trans Kᗮ.reflection, ?_⟩
  intro x hx
  have hsub : L x - T x = -T 0 := by
    have h := T.map_vsub x 0
    simpa [L] using congrArg (fun y : E => y - T x) h
  change Kᗮ.reflection (L x) = T x
  have h := Submodule.reflection_sub ((L.norm_map x).trans (hnorm x hx).symm)
  rw [hsub] at h
  exact h

/-- The root-facet extension required by Lemma D follows from its actual
indexed affine correspondence and the common centred circumsphere. -/
theorem ExactFacetCorrespondence.initial_linear_extension
    {I : Type*} {V V' : I → E} {S : Set I} {c c' : E}
    (D : ExactFacetCorrespondence V V' S c c')
    (hnorm : ∀ i ∈ S, ‖V' i‖ = ‖V i‖) :
    ∃ A : E ≃ₗᵢ[ℝ] E, ∀ i ∈ S, A (V i) = V' i := by
  obtain ⟨A, hA⟩ := affine_isometry_linear_extension D.comparison (V '' S) (by
    rintro _ ⟨i, hi, rfl⟩
    rw [D.comparison_points i hi]
    exact hnorm i hi)
  exact ⟨A, fun i hi => (hA (V i) ⟨i, hi, rfl⟩).trans (D.comparison_points i hi)⟩

/-- The precise spanning input can be supplied in the usual geometric form:
the facet point belongs to the affine span of the ridge and its centre. -/
theorem ridge_centre_span_of_affineSpan (ridge : Set E) (c x : E)
    (hx : x ∈ affineSpan ℝ (insert c ridge)) :
    x - c ∈ Submodule.span ℝ ((fun p => p - c) '' ridge) := by
  have hc : c ∈ affineSpan ℝ (insert c ridge) :=
    subset_affineSpan ℝ _ (Set.mem_insert c ridge)
  have h := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hx hc
  rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_insert c ridge)] at h
  simpa only [Set.image_insert_eq, vsub_self, vsub_eq_sub, sub_self,
    Submodule.span_insert_zero] using h

/-- Affine maps that agree on a ridge and a centre agree on their affine span,
expressed as the linear span of the ridge vectors based at that centre.
This proves the rigidity step without an orientation assumption. -/
theorem affine_rigidity_of_ridge_centre
    (A B : E ≃ᵃⁱ[ℝ] E) (ridge : Set E) (c x : E)
    (hc : A c = B c) (hr : ∀ p ∈ ridge, A p = B p)
    (hx : x - c ∈ Submodule.span ℝ ((fun p => p - c) '' ridge)) :
    A x = B x := by
  have hlinear : Set.EqOn A.linearIsometryEquiv.toLinearMap
      B.linearIsometryEquiv.toLinearMap ((fun p => p - c) '' ridge) := by
    rintro _ ⟨p, hp, rfl⟩
    change A.linearIsometryEquiv (p -ᵥ c) = B.linearIsometryEquiv (p -ᵥ c)
    rw [A.map_vsub, B.map_vsub, hr p hp, hc]
  have h := LinearMap.eqOn_span hlinear hx
  change A.linearIsometryEquiv (x -ᵥ c) = B.linearIsometryEquiv (x -ᵥ c) at h
  rw [A.map_vsub, B.map_vsub, hc] at h
  exact sub_left_injective h

/-- Propagation across one ridge. The tangent geometry contributes only the
equality of centres; exact correspondence and spanning prove point agreement. -/
theorem congruence_across_ridge
    {V V' : I → E} {S : Set I} {c c' : E}
    (D : ExactFacetCorrespondence V V' S c c')
    (A : E ≃ₗᵢ[ℝ] E) (ridge : Set I)
    (ridge_subset : ridge ⊆ S)
    (ridge_agreement : ∀ i ∈ ridge, A (V i) = V' i)
    (centre_agreement : A c = c')
    (ridge_centre_spans : ∀ i ∈ S,
      V i - c ∈ Submodule.span ℝ ((fun j => V j - c) '' ridge)) :
    ∀ i ∈ S, A (V i) = V' i := by
  intro i hi
  have hspan : V i - c ∈ Submodule.span ℝ ((fun p => p - c) '' (V '' ridge)) := by
    simpa only [Set.image_image, Function.comp_def] using ridge_centre_spans i hi
  have h := affine_rigidity_of_ridge_centre A.toAffineIsometryEquiv D.comparison
    (V '' ridge) c (V i)
    (centre_agreement.trans D.comparison_centre.symm) (by
      rintro _ ⟨j, hj, rfl⟩
      exact (ridge_agreement j hj).trans (D.comparison_points j (ridge_subset hj)).symm)
    hspan
  exact h.trans (D.comparison_points i hi)

/-- Paper Lemma D, conditional on the named geometric inputs. The same initial
linear isometry propagates through the entire facet graph. The opposite-side
tangent hypothesis states only the equality of the adjacent facet centres.
No local or global equality of the adjacent vertex sets is assumed. -/
theorem congruence_from_ridge_correspondences
    {F : Type*} (V V' : I → E) (facet : F → Set I)
    (centre centre' : F → E) (adjacent : F → F → Prop)
    (ridge : F → F → Set I)
    (data : ∀ f, ExactFacetCorrespondence V V' (facet f) (centre f) (centre' f))
    (root : F)
    (initial_facet_linear_extension :
      ∃ A : E ≃ₗᵢ[ℝ] E, ∀ i ∈ facet root, A (V i) = V' i)
    (facet_graph_connected : ∀ f, Relation.ReflTransGen adjacent root f)
    (facet_covers : ∀ i, ∃ f, i ∈ facet f)
    (ridge_in_facets : ∀ f g, adjacent f g → ridge f g ⊆ facet f ∩ facet g)
    (ridge_centre_spans : ∀ f g, adjacent f g → ∀ i ∈ facet g,
      V i - centre g ∈ Submodule.span ℝ ((fun j => V j - centre g) '' ridge f g))
    (opposite_side_tangent_centre_unique :
      ∀ (A : E ≃ₗᵢ[ℝ] E) f g, adjacent f g →
        (∀ i ∈ facet f, A (V i) = V' i) → A (centre g) = centre' g) :
    ∃ A : E ≃ₗᵢ[ℝ] E, ∀ i, A (V i) = V' i := by
  obtain ⟨A, hroot⟩ := initial_facet_linear_extension
  refine ⟨A, ?_⟩
  have all_facets : ∀ f, ∀ i ∈ facet f, A (V i) = V' i := by
    intro f
    induction facet_graph_connected f with
    | refl => exact hroot
    | @tail g h _ hgh ih =>
      exact congruence_across_ridge (data h) A (ridge g h)
        (fun _ hi => (ridge_in_facets g h hgh hi).2)
        (fun i hi => ih i (ridge_in_facets g h hgh hi).1)
        (opposite_side_tangent_centre_unique A g h hgh ih)
        (ridge_centre_spans g h hgh)
  intro i
  obtain ⟨f, hi⟩ := facet_covers i
  exact all_facets f i hi

/-- Lemma D with the adjacent-centre equality derived from elementary
projected-plane data. The remaining geometric input constructs the common
plane, tangent feet and strict opposite sides from the two convex figures.
All tangent uniqueness and facet propagation are proved above. -/
theorem congruence_from_tangent_ridge_data
    {F : Type*} (V V' : I → E) (facet : F → Set I)
    (centre centre' : F → E) (adjacent : F → F → Prop)
    (ridge : F → F → Set I)
    (data : ∀ f, ExactFacetCorrespondence V V' (facet f) (centre f) (centre' f))
    (root : F)
    (root_norms : ∀ i ∈ facet root, ‖V' i‖ = ‖V i‖)
    (facet_graph_connected : ∀ f, Relation.ReflTransGen adjacent root f)
    (facet_covers : ∀ i, ∃ f, i ∈ facet f)
    (ridge_in_facets : ∀ f g, adjacent f g → ridge f g ⊆ facet f ∩ facet g)
    (ridge_centre_spans : ∀ f g, adjacent f g → ∀ i ∈ facet g,
      V i - centre g ∈ Submodule.span ℝ ((fun j => V j - centre g) '' ridge f g))
    (opposite_side_projection_data :
      ∀ (A : E ≃ₗᵢ[ℝ] E) f g, adjacent f g →
        (∀ i ∈ facet f, A (V i) = V' i) →
          OppositeTangentData (A (centre g)) (centre' g)) :
    ∃ A : E ≃ₗᵢ[ℝ] E, ∀ i, A (V i) = V' i := by
  exact congruence_from_ridge_correspondences V V' facet centre centre' adjacent ridge
    data root ((data root).initial_linear_extension root_norms)
    facet_graph_connected facet_covers
    ridge_in_facets ridge_centre_spans
    (fun A f g hfg hmatch => (opposite_side_projection_data A f g hfg hmatch).eq)

end Uniform5
