import Uniform5.CompositionLibrarySides
import Uniform5.CompositionFaceOrbits

/-! Actual polygon-orbit witnesses retain both neighboring cell labels. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Transport a concrete model word to any vertex of an actual congruent
uniform facet, moving the polygon and both incident cells by one isometry. -/
theorem modelPolygonWord_at_vertex {K : Set E} (hK : UnitUniform 4 K)
    {M : Set (Space 4)} (hKM : Congruent K M) {k : ℕ} {A B : Set (Space 3)}
    (hword : ModelPolygonWord M k A B) {v : E} (hv : v ∈ K.extremePoints ℝ) :
    ∃ G C D : Set E, PolygonFace K G k ∧ Facet K C ∧ Facet K D ∧
      G ⊆ C ∧ G ⊆ D ∧ C ≠ D ∧ Congruent C A ∧ Congruent D B ∧
      v ∈ G.extremePoints ℝ := by
  obtain ⟨f, hf⟩ := exists_embedding_of_congruent_model (uniform_finitePolytope hK.1)
    (uniform_dimension hK.1) hKM
  obtain ⟨G, C, D, hG, hC, hD, hGC, hGD, hCD, hCA, hDB⟩ := hword
  have hG' : PolygonFace K (f '' G) k := hf ▸ embedding_polygonFace_image f hG
  obtain ⟨g, hg, hgG, hgv⟩ := polygon_orbit_through_vertex
    (uniform_finitePolytope hK.1) (uniform_vertexTransitive hK.1) hG' hv
  refine ⟨g '' (f '' G), g '' (f '' C), g '' (f '' D), hgG, ?_, ?_,
    image_mono (image_mono hGC), image_mono (image_mono hGD), ?_, ?_, ?_, hgv⟩
  · have hh : Facet K (f '' C) := hf ▸ embedding_facet_image f hC
    simpa only [hg] using facet_image g hh
  · have hh : Facet K (f '' D) := hf ▸ embedding_facet_image f hD
    simpa only [hg] using facet_image g hh
  · intro he
    exact hCD (f.injective.image_injective (g.injective.image_injective he))
  · exact congruent_trans (congruent_symm (congruent_affineIsometry_image
      g.toAffineIsometry (f '' C)))
      (congruent_trans (congruent_symm (congruent_affineIsometry_image f C)) hCA)
  · exact congruent_trans (congruent_symm (congruent_affineIsometry_image
      g.toAffineIsometry (f '' D)))
      (congruent_trans (congruent_symm (congruent_affineIsometry_image f D)) hDB)

omit [FiniteDimensional ℝ E] in
/-- Any two distinct pairs exhaust the same two facets above a ridge. -/
theorem TwoContainingFacets.pairs {K G A B C D : Set E}
    (h : TwoContainingFacets K G)
    (hA : Facet K A ∧ G ⊆ A) (hB : Facet K B ∧ G ⊆ B) (hAB : A ≠ B)
    (hC : Facet K C ∧ G ⊆ C) (hD : Facet K D ∧ G ⊆ D) (hCD : C ≠ D) :
    (A = C ∧ B = D) ∨ (A = D ∧ B = C) := by
  obtain ⟨F, H, _, hh⟩ := h
  have ha := (hh A).mp hA
  have hb := (hh B).mp hB
  have hc := (hh C).mp hC
  have hd := (hh D).mp hD
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> tauto

namespace ActualLibraryCycle
variable {N : LibraryNumericalData} {P G : Set (Space 5)} {k : LibraryPolygonSize}
  (A : ActualLibraryCycle N P G k)

/-- Relabel one actual facet by a prescribed congruent model. This is
needed to preserve the exact facet name in a filter requirement. -/
noncomputable def relabelFacet (i : Fin A.cycle.length) (f : CanonicalFacetName)
    (hf : Congruent (A.cycle.facet i) (N.model f)) : ActualLibraryCycle N P G k := by
  classical
  let L : CycleModelLabels A.cycle CellType CanonicalFacetName :=
    { A.labels with
      facetModel := N.model
      facetLabel := fun j => if j = i then f else A.labels.facetLabel j
      facet_matches := by
        intro j
        split_ifs with h
        · subst j
          exact hf
        · simpa only [A.facets] using A.labels.facet_matches j }
  exact ⟨A.cycle, L, A.geometry, A.cells, rfl, A.closed⟩

@[simp] theorem relabelFacet_label (i : Fin A.cycle.length) (f : CanonicalFacetName)
    (hf : Congruent (A.cycle.facet i) (N.model f)) :
    (A.relabelFacet i f hf).labels.facetLabel i = f := by
  classical
  simp [relabelFacet]

/-- Cell names are intrinsic congruence classes, so a genuine additional
model match forces equality of labels, independently of representative choice. -/
theorem cellLabel_eq_of_congruent (i : ℕ) (c : CellType)
    (hc : Congruent (A.cycle.cell i) (cellTypeModel c)) : A.labels.cellLabel i = c := by
  have hm := A.labels.cell_matches i
  rw [A.cells] at hm
  have hh := cellType_eq_iff.mpr (congruent_trans (congruent_symm hm) hc)
  simpa only [cellType_of_model] using hh

end ActualLibraryCycle
end Uniform5.Composition
