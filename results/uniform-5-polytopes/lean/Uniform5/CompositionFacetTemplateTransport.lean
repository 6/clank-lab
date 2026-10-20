import Uniform5.CompositionCellFigureModel

/-! A single whole-facet embedding transports its template and every cell
ridge together. Cell labels refer to the same actual faces in all cycles. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- The actual facet match keeps the template's ridge labels, not just its
unmarked figure shape. All template cells use the same affine isometry. -/
theorem unitUniform5_facet_template_embedding {P K : Set (Space 5)}
    (hP : UnitUniform 5 P) (hK : Facet P K) {v : Space 5}
    (hv : v ∈ K.extremePoints ℝ) (N : LibraryNumericalData) (hLIB : LIB N)
    {n : CanonicalFacetName} (hn : Congruent K (N.model n)) :
    let Q := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    ∃ f : Space 4 →ᵃⁱ[ℝ] Space 5,
      f '' N.model n = K ∧ f (N.baseVertex n) = v ∧
      f '' N.figureModel n = K ∩ Q ∧
      ∀ C, Facet (N.model n) C → N.baseVertex n ∈ C →
        IsConvexFace P (f '' C) ∧ affineDimension (f '' C) = 3 ∧
        f '' (C ∩ N.figureModel n) = (f '' C) ∩ Q ∧
        Congruent C (cellTypeModel (globalCellLabel (f '' C))) := by
  dsimp only
  have hUK : UnitUniform 4 K := ⟨uniform_facets hP.1 hK,
    unitEdges_face (uniform_finitePolytope hP.1) hK.1 hP.2⟩
  have hM := (unitUniform_cross_congruent_iff hn 4).mp hUK
  obtain ⟨f, hf, hfv⟩ := exists_vertex_matched_embedding (n := 1)
    hUK hn hv (hLIB.baseVertex_extreme n)
  have hc := embedding_vertexCentroid f (uniform_finitePolytope hM.1)
  have hvertices : vertices (f '' N.model n)
      ((finitePolytope_affineIsometry_image_iff f (N.model n)).mpr
        (uniform_finitePolytope hM.1)) = vertices K (uniform_finitePolytope hUK.1) := by
    apply Finset.coe_injective
    simp only [coe_vertices, hf]
  have hcenter : f (vertexCentroid (N.vertexSet n)) =
      vertexCentroid (vertices K (uniform_finitePolytope hUK.1)) := by
    rw [hLIB.vertexSet_eq n (uniform_finitePolytope hM.1)]
    exact hc.trans (congrArg vertexCentroid hvertices)
  have hfig : f '' N.figureModel n = K ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) := by
    rw [LibraryNumericalData.figureModel, embedding_vertexFigure, hf, hfv, hcenter]
    exact (uniform_vertexFigure_face_inter hP.1 hK.1 hK.2.1 hv.1).symm
  refine ⟨f, hf, hfv, hfig, ?_⟩
  intro C hC _
  have hCK : Facet K (f '' C) := hf ▸ embedding_facet_image f hC
  have hCP : IsConvexFace P (f '' C) := face_of_face hK.1 hCK.1
  have hd : affineDimension (f '' C) = 3 := by
    have hh := hCK.2.2
    rw [uniform_dimension hUK.1] at hh
    omega
  have hmatch := globalCellLabel_matches (f '' C)
    (exists_actual_cellType (finitePolytope_facet (uniform_finitePolytope hUK.1) hCK) hd)
  refine ⟨hCP, hd, ?_, congruent_trans (congruent_affineIsometry_image f C) hmatch⟩
  rw [image_inter f.injective, hfig]
  ext x
  constructor
  · rintro ⟨hx, _, hq⟩
    exact ⟨hx, hq⟩
  · rintro ⟨hx, hq⟩
    exact ⟨hx, hCK.1.2.1 hx, hq⟩

end Uniform5.Composition
