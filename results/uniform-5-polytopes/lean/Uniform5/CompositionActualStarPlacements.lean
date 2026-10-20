import Uniform5.CompositionU3StarData
import Uniform5.CompositionNormalizedFaceTemplates
import Uniform5.CompositionStarHull

/-! Actual whole facets, with their template placements, indexed by the
facets of a normalized vertex figure. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

/-- All properties of one whole facet placement are obtained from the
actual parent polytope. The figure face and its global label are retained. -/
theorem actual_normalized_facet_placement
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (N : LibraryNumericalData) (hLIB : LIB N)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) {Q F : Set (Space 4)}
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
    (hF : Facet Q F) :
    let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    ∃ p : U3PlacedFacet, p.figureFace = F ∧
      p.name = normalizedFigureFacetLabel N P v V f F ∧
      Facet P (p.placement '' N.model p.name) ∧
      v ∈ p.placement '' N.model p.name ∧
      p.placement (N.baseVertex p.name) = v ∧
      p.placement '' N.figureModel p.name = f '' F ∧
      (p.placement '' N.model p.name) ∩ V = f '' F := by
  dsimp only
  let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
  have hiF : Facet V (f '' F) := by
    change Facet (vertexFigure P v _) (f '' F)
    rw [← him]
    exact embedding_facet_image f hF
  obtain ⟨K, ⟨hK, hvK, hKF⟩, _⟩ :=
    (unitUniform_vertexFigure_facet_correspondence (n := 2) hP hv).2 _ hiF
  have hvK' : v ∈ K.extremePoints ℝ := (face_extremePoints_eq hK.1).symm ▸ ⟨hvK, hv⟩
  have hm := unitUniform5_smallFaces_globalFacetLabel
    classification3D classification4D hP hs N hLIB hK
  obtain ⟨g, hg, hgv, hgfig, _⟩ := unitUniform5_facet_template_embedding hP hK hvK' N hLIB hm
  have hn : globalFacetLabel N K = normalizedFigureFacetLabel N P v V f F := by
    unfold normalizedFigureFacetLabel
    rw [← hKF]
    exact (parentFigureFacetLabel_section (n := 2) hP hv hK.1 hvK N).symm
  refine ⟨⟨globalFacetLabel N K, g, F⟩, rfl, hn, ?_, ?_, hgv, ?_, ?_⟩
  · simpa only [hg] using hK
  · simpa only [hg] using hvK
  · exact hgfig.trans hKF
  · simpa only [hg] using hKF

/-- Actual facets are a finite index type, without an externally supplied
facet enumeration. -/
noncomputable def actualFigureFacetFintype {Q : Set (Space 4)} (hQ : FinitePolytope Q) :
    Fintype {F : Set (Space 4) // Facet Q F} :=
  Set.Finite.fintype ((finitePolytope_faces_finite hQ).subset (fun _ h => h.1))

/-- Exact placement properties for one indexed normalized facet. This is a
predicate on raw data; the preceding theorem proves an inhabitant. -/
def ActualStarPlacement (N : LibraryNumericalData) (P : Set (Space 5)) (v : Space 5)
    (V : Set (Space 5)) (f : Space 4 →ᵃⁱ[ℝ] Space 5) (F : Set (Space 4))
    (p : U3PlacedFacet) : Prop :=
  p.figureFace = F ∧ p.name = normalizedFigureFacetLabel N P v V f F ∧
    Facet P (p.placement '' N.model p.name) ∧ v ∈ p.placement '' N.model p.name ∧
    p.placement (N.baseVertex p.name) = v ∧
    p.placement '' N.figureModel p.name = f '' F ∧
    (p.placement '' N.model p.name) ∩ V = f '' F

/-- Indexing every normalized figure facet yields all actual incident
parent facets, with no missing facet or additional whole-polytope premise. -/
theorem actual_placed_facets_complete {P : Set (Space 5)} (hP : UnitUniform 5 P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) (N : LibraryNumericalData)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) {Q : Set (Space 4)}
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
    (p : {F : Set (Space 4) // Facet Q F} → U3PlacedFacet)
    (hp : ∀ F, ActualStarPlacement N P v
      (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
      f F.val (p F)) :
    Set.range (fun F => (p F).placement '' N.model (p F).name) = facetStar P v := by
  let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
  ext K
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨(hp F).2.2.1, (hp F).2.2.2.1⟩
  · intro hK
    have hsection : Facet V (K ∩ V) :=
      (unitUniform_vertexFigure_facet_correspondence (n := 2) hP hv).1 K hK.1 hK.2
    have hsub : K ∩ V ⊆ Set.range f := by
      rintro x ⟨_, hx⟩
      change x ∈ vertexFigure P v _ at hx
      rw [← him] at hx
      exact Set.image_subset_range _ _ hx
    let H := f ⁻¹' (K ∩ V)
    have himH : f '' H = K ∩ V := Set.image_preimage_eq_of_subset hsub
    have hH : Facet Q H := by
      apply embedding_facet_preimage f
      rw [him]
      exact hsection
    let F : {F : Set (Space 4) // Facet Q F} := ⟨H, hH⟩
    refine ⟨F, ?_⟩
    have hsec : ((p F).placement '' N.model (p F).name) ∩ V = K ∩ V :=
      (hp F).2.2.2.2.2.2.trans himH
    exact ((unitUniform_vertexFigure_section_subset_iff hP hv
      (hp F).2.2.1.1 hK.1.1 (hp F).2.2.2.1 hK.2).mp hsec.subset).antisymm
      ((unitUniform_vertexFigure_section_subset_iff hP hv hK.1.1
        (hp F).2.2.1.1 hK.2 (hp F).2.2.2.1).mp hsec.symm.subset)

end Uniform5.Composition
