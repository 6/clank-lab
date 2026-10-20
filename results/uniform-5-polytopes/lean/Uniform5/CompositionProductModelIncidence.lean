import Uniform5.CompositionModelIncidence
import Uniform5.CompositionProductAssociativity

/-! Actual polygon words transport to concrete product models without
changing their polygon parameter, adjacent cells, or distinctness. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem actual_word_in_congruent_product_model {a b : ℕ} (hab : a + b = 4)
    {K G A B : Set E} {k : ℕ}
    (hK : UnitUniform 4 K) (hG : PolygonFace K G k)
    (hA : Facet K A) (hB : Facet K B) (hGA : G ⊆ A) (hGB : G ⊆ B) (hAB : A ≠ B)
    {M : Set (EuclideanSpace ℝ (Fin a ⊕ Fin b))} (hKM : Congruent K M) :
    ∃ G' A' B' : Set (EuclideanSpace ℝ (Fin a ⊕ Fin b)),
      PolygonFace M G' k ∧ Facet M A' ∧ Facet M B' ∧
      G' ⊆ A' ∧ G' ⊆ B' ∧ A' ≠ B' ∧ Congruent G G' ∧ Congruent A A' ∧ Congruent B B' := by
  have hKN := congruent_trans hKM
    (congruent_affineIsometry_image (flattenProduct a b).toAffineIsometry M)
  obtain ⟨f, hf⟩ := exists_embedding_of_congruent_model (uniform_finitePolytope hK.1)
    ((uniform_dimension hK.1).trans hab.symm) hKN
  let j := f.comp (flattenProduct a b).toAffineIsometry
  have hj : j '' M = K := by
    change (f ∘ flattenProduct a b) '' M = K
    rw [Set.image_comp]
    exact hf
  have hM := (unitUniform_cross_congruent_iff hKM 4).mp hK
  have hGf : PolygonFace (j '' M) G k := hj ▸ hG
  have hAf : Facet (j '' M) A := hj ▸ hA
  have hBf : Facet (j '' M) B := hj ▸ hB
  have hiG := embedding_face_image_preimage j hGf.1
  have hiA := embedding_face_image_preimage j hAf.1
  have hiB := embedding_face_image_preimage j hBf.1
  refine ⟨j ⁻¹' G, j ⁻¹' A, j ⁻¹' B,
    embedding_polygonFace_preimage j (uniform_finitePolytope hM.1) hGf,
    embedding_facet_preimage j hAf, embedding_facet_preimage j hBf,
    Set.preimage_mono hGA, Set.preimage_mono hGB, ?_, ?_, ?_, ?_⟩
  · intro he
    apply hAB
    rw [← hiA, ← hiB, he]
  · have hc := congruent_affineIsometry_image j (j ⁻¹' G)
    rw [hiG] at hc
    exact congruent_symm hc
  · have hc := congruent_affineIsometry_image j (j ⁻¹' A)
    rw [hiA] at hc
    exact congruent_symm hc
  · have hc := congruent_affineIsometry_image j (j ⁻¹' B)
    rw [hiB] at hc
    exact congruent_symm hc

end Uniform5.Composition
