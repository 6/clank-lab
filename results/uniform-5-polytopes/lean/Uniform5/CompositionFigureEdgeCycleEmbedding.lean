import Uniform5.CompositionFigureEdgeCycle
import Uniform5.CompositionEmbedding

/-! Complete edge-incidence cycles reflect through actual affine-isometric
coordinate embeddings, preserving their original cyclic indices. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

namespace ActualEdgeIncidenceCycle

noncomputable def pullback (f : E →ᵃⁱ[ℝ] F) {Q : Set E} {e : Set F} {n : ℕ}
    (D : ActualEdgeIncidenceCycle (f '' Q) e n) :
    ActualEdgeIncidenceCycle Q (f ⁻¹' e) n := by
  have him {A : Set F} (hA : IsConvexFace (f '' Q) A) : f '' (f ⁻¹' A) = A :=
    embedding_face_image_preimage f hA
  have hdim {A : Set F} (hA : IsConvexFace (f '' Q) A) :
      affineDimension (f ⁻¹' A) = affineDimension A := by
    rw [← affineDimension_affineIsometry_image f, him hA]
  have hpre (A : Set E) : f ⁻¹' (f '' A) = A := Set.preimage_image_eq A f.injective
  have hsub {A : Set F} (hA : IsConvexFace (f '' Q) A) {B : Set E} :
      f ⁻¹' A ⊆ B ↔ A ⊆ f '' B := by
    constructor
    · intro h
      rw [← him hA]
      exact Set.image_mono h
    · intro h x hx
      exact f.injective.mem_set_image.mp (h hx)
  refine {
    polytope := (finitePolytope_affineIsometry_image_iff f Q).mp D.polytope
    dimension := by rw [← affineDimension_affineIsometry_image f]; exact D.dimension
    edge_face := embedding_face_preimage f D.edge_face
    edge_nonempty := Set.Nonempty.of_image ((him D.edge_face).symm ▸ D.edge_nonempty)
    edge_dimension := (hdim D.edge_face).trans D.edge_dimension
    length_ge := D.length_ge
    ridge := fun i => f ⁻¹' D.ridge i
    ridge_face := fun i => embedding_face_preimage f (D.ridge_face i)
    ridge_contains := fun i => Set.preimage_mono (D.ridge_contains i)
    ridge_dimension := fun i => (hdim (D.ridge_face i)).trans (D.ridge_dimension i)
    ridge_closed := congrArg (fun A => f ⁻¹' A) D.ridge_closed
    ridge_injective := ?_
    ridge_coverage := ?_
    facet := fun i => f ⁻¹' D.facet i
    facet_incidence := fun i => ⟨embedding_facet_preimage f (D.facet_incidence i).1,
      Set.preimage_mono (D.facet_incidence i).2.1,
      Set.preimage_mono (D.facet_incidence i).2.2.1,
      Set.preimage_mono (D.facet_incidence i).2.2.2⟩
    facet_injective := ?_
    facet_coverage := ?_
    facets_at_ridge := ?_
    consecutive_unique := ?_ }
  · intro i hi j hj hh
    apply D.ridge_injective hi hj
    have he := congrArg (fun A => f '' A) hh
    simpa only [him (D.ridge_face i), him (D.ridge_face j)] using he
  · intro H hH heH hdH
    obtain ⟨i, hi, hiH⟩ := D.ridge_coverage (f '' H) (embedding_face_image f hH)
      ((hsub D.edge_face).mp heH) (by rwa [affineDimension_affineIsometry_image])
    exact ⟨i, hi, by rw [hiH, hpre]⟩
  · intro i j hh
    apply D.facet_injective
    have he := congrArg (fun A => f '' A) hh
    simpa only [him (D.facet_incidence i).1.1, him (D.facet_incidence j).1.1] using he
  · intro H
    constructor
    · rintro ⟨hH, heH⟩
      obtain ⟨i, hi⟩ := (D.facet_coverage (f '' H)).mp
        ⟨embedding_facet_image f hH, (hsub D.edge_face).mp heH⟩
      exact ⟨i, by rw [hi, hpre]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨embedding_facet_preimage f (D.facet_incidence i).1,
        Set.preimage_mono (D.facet_incidence i).2.1⟩
  · intro i H
    constructor
    · rintro ⟨hH, hrH⟩
      rcases (D.facets_at_ridge i (f '' H)).mp
        ⟨embedding_facet_image f hH, (hsub (D.ridge_face i)).mp hrH⟩ with h | h
      · exact Or.inl (by rw [← h, hpre])
      · exact Or.inr (by rw [← h, hpre])
    · intro hh
      rcases hh with rfl | rfl
      · have hh := (D.facets_at_ridge i _).mpr (Or.inl rfl)
        exact ⟨embedding_facet_preimage f hh.1, Set.preimage_mono hh.2⟩
      · have hh := (D.facets_at_ridge i _).mpr (Or.inr rfl)
        exact ⟨embedding_facet_preimage f hh.1, Set.preimage_mono hh.2⟩
  · intro i
    obtain ⟨A, ⟨hA, hCA, hCB⟩, hu⟩ := D.consecutive_unique i
    refine ⟨f ⁻¹' A, ⟨embedding_facet_preimage f hA,
      Set.preimage_mono hCA, Set.preimage_mono hCB⟩, ?_⟩
    rintro H ⟨hH, hCH, hCH'⟩
    have he := hu (f '' H) ⟨embedding_facet_image f hH,
      (hsub (D.ridge_face i)).mp hCH, (hsub (D.ridge_face (i.val + 1))).mp hCH'⟩
    rw [← he, hpre]

@[simp] theorem pullback_ridge (f : E →ᵃⁱ[ℝ] F) {Q : Set E} {e : Set F} {n : ℕ}
    (D : ActualEdgeIncidenceCycle (f '' Q) e n) (i : ℕ) :
    (D.pullback f).ridge i = f ⁻¹' D.ridge i := rfl

@[simp] theorem pullback_facet (f : E →ᵃⁱ[ℝ] F) {Q : Set E} {e : Set F} {n : ℕ}
    (D : ActualEdgeIncidenceCycle (f '' Q) e n) (i : Fin n) :
    (D.pullback f).facet i = f ⁻¹' D.facet i := rfl

noncomputable def pullbackOfImage (f : E →ᵃⁱ[ℝ] F) {Q : Set E} {V e : Set F} {n : ℕ}
    (D : ActualEdgeIncidenceCycle V e n) (h : f '' Q = V) :
    ActualEdgeIncidenceCycle Q (f ⁻¹' e) n :=
  (h.symm ▸ D).pullback f

@[simp] theorem pullbackOfImage_ridge (f : E →ᵃⁱ[ℝ] F)
    {Q : Set E} {V e : Set F} {n : ℕ} (D : ActualEdgeIncidenceCycle V e n)
    (h : f '' Q = V) (i : ℕ) :
    (D.pullbackOfImage f h).ridge i = f ⁻¹' D.ridge i := by subst V; rfl

@[simp] theorem pullbackOfImage_facet (f : E →ᵃⁱ[ℝ] F)
    {Q : Set E} {V e : Set F} {n : ℕ} (D : ActualEdgeIncidenceCycle V e n)
    (h : f '' Q = V) (i : Fin n) :
    (D.pullbackOfImage f h).facet i = f ⁻¹' D.facet i := by subst V; rfl

noncomputable def castEdge {Q e e' : Set E} {n : ℕ}
    (D : ActualEdgeIncidenceCycle Q e n) (h : e = e') : ActualEdgeIncidenceCycle Q e' n := h ▸ D

@[simp] theorem castEdge_ridge {Q e e' : Set E} {n : ℕ}
    (D : ActualEdgeIncidenceCycle Q e n) (h : e = e') (i : ℕ) :
    (D.castEdge h).ridge i = D.ridge i := by subst e'; rfl

@[simp] theorem castEdge_facet {Q e e' : Set E} {n : ℕ}
    (D : ActualEdgeIncidenceCycle Q e n) (h : e = e') (i : Fin n) :
    (D.castEdge h).facet i = D.facet i := by subst e'; rfl

end ActualEdgeIncidenceCycle
end Uniform5.Composition
