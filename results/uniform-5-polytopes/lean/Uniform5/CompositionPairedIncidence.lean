import Uniform5.CompositionFacetSystemGeneral

/-! Apply the finite paired-fan incidence arguments to the genuine edge
and facet sets of a four-dimensional finite polytope. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def actualVertexEmbedding {Q : Set E} (hQ : FinitePolytope Q)
    {k : ℕ} (p : Fin k ↪ E) (hp : ∀ i, p i ∈ Q.extremePoints ℝ) :
    Fin k ↪ vertices Q hQ where
  toFun i := ⟨p i, (mem_vertices hQ _).mpr (hp i)⟩
  inj' := fun _ _ h => p.injective (congrArg Subtype.val h)

noncomputable def actualVertexSubset {Q : Set E} (hQ : FinitePolytope Q)
    (S : Set E) : Finset (vertices Q hQ) := Finset.univ.filter (fun x => (x : E) ∈ S)

@[simp] theorem mem_actualVertexSubset {Q : Set E} (hQ : FinitePolytope Q)
    (S : Set E) (x : vertices Q hQ) : x ∈ actualVertexSubset hQ S ↔ (x : E) ∈ S := by
  simp [actualVertexSubset]

private theorem actual_fan_subset {Q : Set E} (hQ : FinitePolytope Q)
    {k : ℕ} (p : Fin k ↪ E) (hp : ∀ i, p i ∈ Q.extremePoints ℝ)
    (S : Set E) (a b : Fin k)
    (hfan : ∀ F, Facet Q F → p a ∈ F → p b ∈ F → F.extremePoints ℝ ⊆ S) :
    ∀ F, actualVertexEmbedding hQ p hp a ∈ (actualFacetSystem Q hQ).vertices F →
      actualVertexEmbedding hQ p hp b ∈ (actualFacetSystem Q hQ).vertices F →
      (actualFacetSystem Q hQ).vertices F ⊆ actualVertexSubset hQ S := by
  intro F ha hb x hx
  apply (mem_actualVertexSubset hQ S x).mpr
  apply hfan F.val F.property
    ((mem_actualFacetSystem_vertices Q hQ F _).mp ha)
    ((mem_actualFacetSystem_vertices Q hQ F _).mp hb)
  rw [face_extremePoints_eq F.property.1]
  exact ⟨(mem_actualFacetSystem_vertices Q hQ F x).mp hx,
    (mem_vertices hQ x).mp x.property⟩

private theorem actual_neighbours_four {Q : Set E} (hQ : FinitePolytope Q)
    {k : ℕ} (p : Fin k ↪ E) (hp : ∀ i, p i ∈ Q.extremePoints ℝ)
    (a b c d e : Fin k)
    (he : ∀ z, Edge Q (p a) z ↔ z = p b ∨ z = p c ∨ z = p d ∨ z = p e) :
    (actualFacetSystem Q hQ).neighbours (actualVertexEmbedding hQ p hp a) =
      {actualVertexEmbedding hQ p hp b, actualVertexEmbedding hQ p hp c,
        actualVertexEmbedding hQ p hp d, actualVertexEmbedding hQ p hp e} := by
  ext z
  rw [CaseB.FacetSystem.mem_neighbours]
  change Edge Q (p a) (z : E) ↔ _
  rw [he]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
  · rintro (rfl | rfl | rfl | rfl) <;> simp [actualVertexEmbedding]

/-- Actual k3 simple-vertex step: the fifth point is forced into the
partner fan. No combinatorial incidence laws are assumed. -/
theorem finitePolytope_paired_k3_vertex_in_partner {Q : Set E}
    (hQ : FinitePolytope Q) (hd : affineDimension Q = 4)
    (p : Fin 5 ↪ E) (hp : ∀ i, p i ∈ Q.extremePoints ℝ) (S : Set E)
    (hfan : ∀ F, Facet Q F → p 2 ∈ F → p 3 ∈ F → F.extremePoints ℝ ⊆ S)
    (hoff : p 4 ∉ S → ∀ z, Edge Q (p 4) z ↔
      z = p 0 ∨ z = p 1 ∨ z = p 2 ∨ z = p 3) : p 4 ∈ S := by
  let q := actualVertexEmbedding hQ p hp
  have h := CaseB.paired_k3_vertex_in_partner (actualFacetSystem Q hQ)
    (actualFacetSystem_general_laws hQ hd) q (actualVertexSubset hQ S)
    (actual_fan_subset hQ p hp S 2 3 hfan) (fun hh =>
      actual_neighbours_four hQ p hp 4 0 1 2 3
        (hoff (fun hz => hh ((mem_actualVertexSubset hQ S (q 4)).mpr hz))))
  exact (mem_actualVertexSubset hQ S (q 4)).mp h

/-- Actual k4 simple-vertex step: at least one of the two extra points
is forced into the partner fan. -/
theorem finitePolytope_paired_k4_escape {Q : Set E}
    (hQ : FinitePolytope Q) (hd : affineDimension Q = 4)
    (p : Fin 6 ↪ E) (hp : ∀ i, p i ∈ Q.extremePoints ℝ) (S : Set E)
    (hfan : ∀ F, Facet Q F → p 2 ∈ F → p 3 ∈ F → F.extremePoints ℝ ⊆ S)
    (hu : p 4 ∉ S → ∀ z, Edge Q (p 4) z ↔
      z = p 0 ∨ z = p 1 ∨ z = p 3 ∨ z = p 5)
    (hv : p 5 ∉ S → ∀ z, Edge Q (p 5) z ↔
      z = p 0 ∨ z = p 1 ∨ z = p 4 ∨ z = p 2) : p 4 ∈ S ∨ p 5 ∈ S := by
  let q := actualVertexEmbedding hQ p hp
  have h := CaseB.paired_k4_escape (actualFacetSystem Q hQ)
    (actualFacetSystem_general_laws hQ hd) q (actualVertexSubset hQ S)
    (actual_fan_subset hQ p hp S 2 3 hfan)
    (fun hh => actual_neighbours_four hQ p hp 4 0 1 3 5
      (hu (fun hz => hh ((mem_actualVertexSubset hQ S (q 4)).mpr hz))))
    (fun hh => actual_neighbours_four hQ p hp 5 0 1 4 2
      (hv (fun hz => hh ((mem_actualVertexSubset hQ S (q 5)).mpr hz))))
  exact h.imp ((mem_actualVertexSubset hQ S (q 4)).mp)
    ((mem_actualVertexSubset hQ S (q 5)).mp)

end Uniform5.Composition
