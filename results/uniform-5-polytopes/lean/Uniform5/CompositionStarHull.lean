import Uniform5.CompositionStars
import Uniform5.CompositionFigureNormalization
import Uniform5.CompositionRidgeSpanning

/-! The convex hull of an actual vertex star is full dimensional and has
all incident parent facets as genuine facets. This establishes convex
placement for the geometric objects enumerated by stage three. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

noncomputable def facetStarHull (P : Set (Space 5)) (v : Space 5) : Set (Space 5) :=
  convexHull ℝ {x | ∃ F ∈ facetStar P v, x ∈ F}

theorem facetStarHull_subset {P : Set (Space 5)} (hP : FinitePolytope P) (v : Space 5) :
    facetStarHull P v ⊆ P := by
  apply convexHull_min
  · rintro x ⟨F, hF, hx⟩
    exact hF.1.1.2.1 hx
  · exact finitePolytope_convex hP

theorem facet_subset_facetStarHull {P F : Set (Space 5)} {v : Space 5}
    (hF : F ∈ facetStar P v) : F ⊆ facetStarHull P v := by
  intro x hx
  exact subset_convexHull ℝ _ ⟨F, hF, hx⟩

/-- The figure and apex already span the original five-dimensional space;
both lie in the convex hull of the full incident facets. -/
theorem unitUniform5_facetStarHull_span {P : Set (Space 5)} (hP : UnitUniform 5 P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) :
    affineSpan ℝ (facetStarHull P v) = ⊤ := by
  let hPP := uniform_finitePolytope hP.1
  let c := vertexCentroid (vertices P hPP)
  let V := vertexFigure P v c
  obtain ⟨_, hR, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have hRpos := uniform_intrinsicRadius_pos hP.1
  have hsq : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = intrinsicRadius P ^ 2 := hs
  have hV : FinitePolytope V := finitePolytope_vertexFigure_of_positiveDimension hPP hv c
    (intrinsicRadius P) hsq hP.2 (by rw [uniform_dimension hP.1]; omega)
  have hdV : affineDimension V = 4 := by
    have hd := finitePolytope_unit_vertexFigure_dimension hPP hv c (intrinsicRadius P)
      hsq hP.2 (by simpa using uniform_dimension hP.1) (by simp)
    simpa [V, Space] using hd
  have heq : V = convexHull ℝ {z | Edge P v z} :=
    finitePolytope_unit_vertexFigure hPP hv c (intrinsicRadius P) hsq hP.2
  have hnei : {z | Edge P v z}.Nonempty := by
    rw [← convexHull_nonempty_iff (𝕜 := ℝ), ← heq]
    exact finitePolytope_nonempty hV
  have hnear : {z | Edge P v z} ⊆ facetStarHull P v := by
    intro z hz
    obtain ⟨F, hF, hvF, hzF⟩ := edge_mem_facet hPP hz
      (by rw [uniform_dimension hP.1]; norm_num)
    exact facet_subset_facetStarHull ⟨hF, hvF⟩ hzF
  have hVH : V ⊆ facetStarHull P v := by
    rw [heq]
    exact convexHull_min hnear (convex_convexHull ℝ _)
  obtain ⟨w, hw⟩ := hnei
  obtain ⟨F, hF, hvF, _⟩ := edge_mem_facet hPP hw
    (by rw [uniform_dimension hP.1]; norm_num)
  have hvH : v ∈ facetStarHull P v := facet_subset_facetStarHull ⟨hF, hvF⟩ hvF
  have hvout : v ∉ affineSpan ℝ V := by
    intro hh
    have hplane := unitUniform5_vertexFigure_affineSpan hP (intrinsicRadius P) hRpos hsq hv
    have he : ⟪v - c, v - c⟫ = intrinsicRadius P ^ 2 - 1 / 2 := by
      change v ∈ (affineSpan ℝ V : Set (Space 5)) at hh
      change (affineSpan ℝ V : Set (Space 5)) = _ at hplane
      rw [hplane] at hh
      exact hh
    rw [real_inner_self_eq_norm_sq] at he
    have hvnorm := hsq v hv
    linarith
  have hspan : affineSpan ℝ (insert v V) = affineSpan ℝ P :=
    affineSpan_insert_eq_of_dimension_gap (fun _ hx => hx.1)
      (finitePolytope_nonempty hV) (by rw [hdV, uniform_dimension hP.1]) hv.1 hvout
  apply top_unique
  rw [← uniform5_affineSpan_eq_top hP.1, ← hspan]
  exact affineSpan_mono ℝ (Set.insert_subset hvH hVH)

theorem unitUniform5_facetStarHull_dimension {P : Set (Space 5)}
    (hP : UnitUniform 5 P) {v : Space 5} (hv : v ∈ P.extremePoints ℝ) :
    affineDimension (facetStarHull P v) = 5 := by
  unfold affineDimension Uniform5.affineDimension
  rw [unitUniform5_facetStarHull_span hP hv, AffineSubspace.direction_top, finrank_top]
  exact finrank_euclideanSpace_fin

/-- Restriction of an actual incident facet to the star hull is still a
facet, with its full vertex set unchanged. -/
theorem unitUniform5_facetStarHull_facet {P F : Set (Space 5)}
    (hP : UnitUniform 5 P) {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (hF : F ∈ facetStar P v) : Facet (facetStarHull P v) F := by
  refine ⟨face_restrict hF.1.1 (facetStarHull_subset (uniform_finitePolytope hP.1) v)
    (facet_subset_facetStarHull hF), hF.1.2.1, ?_⟩
  rw [unitUniform5_facetStarHull_dimension hP hv]
  exact hF.1.2.2.trans (uniform_dimension hP.1)


/-- Taking the neighbor section commutes with restricting to the actual
whole incident-facet hull. -/
theorem unitUniform5_facetStarHull_figure {P : Set (Space 5)}
    (hP : UnitUniform 5 P) {v : Space 5} (hv : v ∈ P.extremePoints ℝ) :
    vertexFigure (facetStarHull P v) v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) =
    vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) := by
  let hPP := uniform_finitePolytope hP.1
  let c := vertexCentroid (vertices P hPP)
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have heq := finitePolytope_unit_vertexFigure hPP hv c (intrinsicRadius P) hs hP.2
  have hnear : {z | Edge P v z} ⊆ facetStarHull P v := by
    intro z hz
    obtain ⟨F, hF, hvF, hzF⟩ := edge_mem_facet hPP hz
      (by rw [uniform_dimension hP.1]; norm_num)
    exact facet_subset_facetStarHull ⟨hF, hvF⟩ hzF
  have hsub : vertexFigure P v c ⊆ facetStarHull P v := by
    rw [heq]
    exact convexHull_min hnear (convex_convexHull ℝ _)
  ext x
  constructor
  · intro hx
    exact ⟨facetStarHull_subset hPP v hx.1, hx.2⟩
  · intro hx
    exact ⟨hsub hx, hx.2⟩

end Uniform5.Composition
