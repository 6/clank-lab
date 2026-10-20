import Uniform5.CompositionCrossCongruence

/-! Transport of actual polygon words to concrete intrinsic facet models. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- An intrinsically congruent model in the actual affine dimension embeds
into the original ambient space with exactly the original hull as image. -/
theorem exists_embedding_of_congruent_model {P : Set E} (hP : FinitePolytope P)
    {n : ℕ} (hd : affineDimension P = n) {Q : Set (Space n)} (hPQ : Congruent P Q) :
    ∃ f : Space n →ᵃⁱ[ℝ] E, f '' Q = P := by
  obtain ⟨j, A, hj, hAP⟩ := exists_intrinsic_euclidean_model P (finitePolytope_nonempty hP) n hd
  obtain ⟨g, hg⟩ := (congruent_iff_affineIsometryEquiv_image A Q).mp (congruent_trans hAP hPQ)
  refine ⟨j.comp g.symm.toAffineIsometry, ?_⟩
  change (j ∘ g.symm) '' Q = P
  rw [Set.image_comp, ← hg]
  simpa only [affineIsometry_symm_image_image] using hj

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem embedding_polygonFace_image (f : E →ᵃⁱ[ℝ] F) {P G : Set E} {k : ℕ}
    (hG : PolygonFace P G k) : PolygonFace (f '' P) (f '' G) k := by
  classical
  obtain ⟨V, hV, hk⟩ := hG.2.2
  refine ⟨embedding_face_image f hG.1, ?_, V.image f, ?_, ?_⟩
  · rw [affineDimension_affineIsometry_image, hG.2.1]
  · rw [Finset.coe_image, hV, embedding_extremePoints]
  · rw [Finset.card_image_of_injective _ f.injective, hk]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem embedding_polygonFace_preimage (f : E →ᵃⁱ[ℝ] F) {P : Set E}
    (hP : FinitePolytope P) {G : Set F} {k : ℕ} (hG : PolygonFace (f '' P) G k) :
    PolygonFace P (f ⁻¹' G) k := by
  have hi := embedding_face_image_preimage f hG.1
  have hne : (f ⁻¹' G).Nonempty := by
    have hh := polygonFace_nonempty hG
    rw [← hi] at hh
    exact hh.of_image
  let hGP := finitePolytope_face hP (embedding_face_preimage f hG.1) hne
  refine ⟨embedding_face_preimage f hG.1, ?_, vertices _ hGP, coe_vertices _ _, ?_⟩
  · rw [← affineDimension_affineIsometry_image f, hi, hG.2.1]
  · have hc := polygonFace_extremePoints_ncard (embedding_polygonFace_image f
      (show PolygonFace P (f ⁻¹' G) (vertices _ hGP).card from
        ⟨embedding_face_preimage f hG.1, by rw [← affineDimension_affineIsometry_image f, hi, hG.2.1],
          vertices _ hGP, coe_vertices _ _, rfl⟩))
    rw [hi] at hc
    exact hc.symm.trans (polygonFace_extremePoints_ncard hG)

/-- A polygon word in an actual facet is a polygon word in every congruent
intrinsic model, with the same actual cell congruence classes. -/
theorem actual_word_in_congruent_model {K G A B : Set E} {k : ℕ}
    (hK : UnitUniform 4 K) (hG : PolygonFace K G k)
    (hA : Facet K A) (hB : Facet K B) (hGA : G ⊆ A) (hGB : G ⊆ B) (hAB : A ≠ B)
    {M : Set (Space 4)} (hKM : Congruent K M) :
    ∃ G' A' B' : Set (Space 4), PolygonFace M G' k ∧ Facet M A' ∧ Facet M B' ∧
      G' ⊆ A' ∧ G' ⊆ B' ∧ A' ≠ B' ∧ Congruent G G' ∧ Congruent A A' ∧ Congruent B B' := by
  obtain ⟨f, hf⟩ := exists_embedding_of_congruent_model (uniform_finitePolytope hK.1)
    (uniform_dimension hK.1) hKM
  have hM := (unitUniform_cross_congruent_iff hKM 4).mp hK
  have hGf : PolygonFace (f '' M) G k := hf ▸ hG
  have hAf : Facet (f '' M) A := hf ▸ hA
  have hBf : Facet (f '' M) B := hf ▸ hB
  have hiG := embedding_face_image_preimage f hGf.1
  have hiA := embedding_face_image_preimage f hAf.1
  have hiB := embedding_face_image_preimage f hBf.1
  refine ⟨f ⁻¹' G, f ⁻¹' A, f ⁻¹' B,
    embedding_polygonFace_preimage f (uniform_finitePolytope hM.1) hGf,
    embedding_facet_preimage f hAf, embedding_facet_preimage f hBf,
    Set.preimage_mono hGA, Set.preimage_mono hGB, ?_, ?_, ?_, ?_⟩
  · intro he
    apply hAB
    rw [← hiA, ← hiB, he]
  · have hc := congruent_affineIsometry_image f (f ⁻¹' G)
    rw [hiG] at hc
    exact congruent_symm hc
  · have hc := congruent_affineIsometry_image f (f ⁻¹' A)
    rw [hiA] at hc
    exact congruent_symm hc
  · have hc := congruent_affineIsometry_image f (f ⁻¹' B)
    rw [hiB] at hc
    exact congruent_symm hc

/-- Semantic occurrence of the library word (K,k,A,B): an actual polygon
between two distinct actual cells with the indicated concrete cell models. -/
noncomputable def ModelPolygonWord (K : Set (Space 4)) (k : ℕ)
    (A B : Set (Space 3)) : Prop :=
  ∃ G C D : Set (Space 4), PolygonFace K G k ∧ Facet K C ∧ Facet K D ∧
    G ⊆ C ∧ G ⊆ D ∧ C ≠ D ∧ Congruent C A ∧ Congruent D B

theorem modelPolygonWord_swap {K : Set (Space 4)} {k : ℕ} {A B : Set (Space 3)}
    (h : ModelPolygonWord K k A B) : ModelPolygonWord K k B A := by
  obtain ⟨G, C, D, hG, hC, hD, hGC, hGD, hCD, hCA, hDB⟩ := h
  exact ⟨G, D, C, hG, hD, hC, hGD, hGC, hCD.symm, hDB, hCA⟩

theorem modelPolygonWord_of_actual {K G A B : Set E} {k : ℕ}
    (hK : UnitUniform 4 K) (hG : PolygonFace K G k)
    (hA : Facet K A) (hB : Facet K B) (hGA : G ⊆ A) (hGB : G ⊆ B) (hAB : A ≠ B)
    {M : Set (Space 4)} {CA CB : Set (Space 3)}
    (hKM : Congruent K M) (hACA : Congruent A CA) (hBCB : Congruent B CB) :
    ModelPolygonWord M k CA CB := by
  obtain ⟨G', A', B', hG', hA', hB', hGA', hGB', hAB', _, hAA', hBB'⟩ :=
    actual_word_in_congruent_model hK hG hA hB hGA hGB hAB hKM
  exact ⟨G', A', B', hG', hA', hB', hGA', hGB', hAB',
    congruent_trans (congruent_symm hAA') hACA, congruent_trans (congruent_symm hBB') hBCB⟩

end Uniform5.Composition
