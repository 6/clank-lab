import Uniform5.CompositionRidgeListInputs
import Uniform5.CompositionNormalizedFaceTemplates

/-! Certified ridge lists on actual normalized facet figures. A single
ambient isometry transports the whole template and all its listed ridges;
the transported label is the same whole-cell label used by the actual figure. -/

noncomputable section
namespace Uniform5.Composition
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem CyclicPolygonBoundary.image {P : Set E} {n : ℕ} {point : Fin n → E}
    (h : CyclicPolygonBoundary P point) (g : E ≃ᵃⁱ[ℝ] E) :
    CyclicPolygonBoundary (g '' P) (fun i => g (point i)) := by
  have hr : Set.range (fun i => g (point i)) = g '' Set.range point := by
    exact Set.range_comp g point
  refine ⟨h.length_ge, ?_, by simpa using h.dimension,
    g.injective.comp h.injective, ?_, fun i => edge_image g (h.consecutive i)⟩
  · rw [h.hull, hr]
    exact g.toAffineMap.image_convexHull _
  · rw [hr, h.vertices, affineIsometry_image_extremePoints]

/-- An intrinsic marked template has an ambient extension retaining every
whole-cell marking under the same map. -/
theorem labeledFacetTemplateMatch_ambient (N : LibraryNumericalData)
    (k : CanonicalFacetName) (F : Set (Space 4)) (labels : Set (Space 4) → CellType)
    (h : LabeledFacetTemplateMatch N k F labels) :
    ∃ g : Space 4 ≃ᵃⁱ[ℝ] Space 4, g '' N.figureModel k = F ∧
      ∀ C, Facet (N.model k) C → N.baseVertex k ∈ C →
        Congruent C (cellTypeModel (labels (g '' (C ∩ N.figureModel k)))) := by
  obtain ⟨e, he⟩ := h
  obtain ⟨g, hg⟩ := isometryEquiv_extends_affineIsometryEquiv e
  have hF : g '' N.figureModel k = F := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hg ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [hg]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
  refine ⟨g, hF, ?_⟩
  intro C hC hvC
  have him : figureTemplateRidge e C = g '' (C ∩ N.figureModel k) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, ⟨hx, x.property⟩, hg x⟩
    · rintro ⟨x, ⟨hxC, hxX⟩, rfl⟩
      exact ⟨⟨x, hxX⟩, hxC, (hg ⟨x, hxX⟩).symm⟩
  simpa only [him] using he C hC hvC

/-- Every actual ridge of a marked template is a listed ridge, with its
actual cyclic boundary and exactly the same whole-cell label. -/
theorem RIDGES.transport (N : LibraryNumericalData) (D : RidgeListData)
    (hR : RIDGES N D) (k : CanonicalFacetName) (F : Set (Space 4))
    (labels : Set (Space 4) → CellType) (hF : LabeledFacetTemplateMatch N k F labels) :
    ∃ g : Space 4 ≃ᵃⁱ[ℝ] Space 4, g '' N.figureModel k = F ∧
      ∀ H, IsConvexFace F H → H.Nonempty → affineDimension H = 2 →
        ∃ r ∈ D.ridges k, g '' r.hull = H ∧
          CyclicPolygonBoundary H (fun i => g (r.point i)) ∧ r.cellLabel = labels H := by
  obtain ⟨g, hg, hlabels⟩ := labeledFacetTemplateMatch_ambient N k F labels hF
  refine ⟨g, hg, ?_⟩
  intro H hH hne hd
  have hpre : IsConvexFace (N.figureModel k) (g.symm '' H) := by
    have hp := isConvexFace_image g.symm hH
    rwa [← hg, affineIsometry_symm_image_image] at hp
  obtain ⟨r, hr, he, hb, C, hC, hvC, hCH, hc⟩ :=
    hR.actual_ridge hpre (hne.image g.symm) (by simpa using hd)
  have him : g '' r.hull = H := by rw [he, affineIsometry_image_symm_image]
  refine ⟨r, hr, him, ?_, ?_⟩
  · simpa only [affineIsometry_image_symm_image] using hb.image g
  · have hl := hlabels C hC hvC
    rw [hCH, affineIsometry_image_symm_image] at hl
    have hm := congruent_trans (congruent_symm hc) hl
    simpa only [cellType_of_model] using cellType_eq_iff.mpr hm

/-- RIDGES applies to the genuine normalized vertex figure, using its
globally coherent parent-cell label function. All template premises follow
from the actual uniform polytope, the cited classifications and LIB. -/
theorem unitUniform5_normalized_facet_ridges
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (N : LibraryNumericalData) (hLIB : LIB N) (D : RidgeListData) (hR : RIDGES N D)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) {Q F : Set (Space 4)}
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
    (hF : Facet Q F) :
    let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    let k := normalizedFigureFacetLabel N P v V f F
    ∃ g : Space 4 ≃ᵃⁱ[ℝ] Space 4, g '' N.figureModel k = F ∧
      ∀ H, IsConvexFace F H → H.Nonempty → affineDimension H = 2 →
        ∃ r ∈ D.ridges k, g '' r.hull = H ∧
          CyclicPolygonBoundary H (fun i => g (r.point i)) ∧
          r.cellLabel = normalizedFigureCellLabel P v V f H := by
  dsimp only
  exact hR.transport N D _ F _
    (actual_normalized_facet_template classification3D classification4D hP hs hv N hLIB f him hF)

end Uniform5.Composition
