import Uniform5.EuclideanPropagation
import Uniform5.CompositionUniformFaces
import Uniform5.CompositionPolygonEdges
import Uniform5.CompositionPolygonSpan
import Uniform5.CompositionEmbedding
import Uniform5.CompositionStars

/-!
# Equivalence of the two geometric interfaces

The recursive hull formulation and the vertex-set formulation describe the
same finite Euclidean polytopes. These bridges identify their facets,
vertex symmetries, regular polygons, recursive uniformity, and unit edges.
-/
noncomputable section
namespace Uniform5.Composition
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem facet_iff_isGeometricFacet {P F : Set E} (hP : FinitePolytope P) :
    Facet P F ↔ IsGeometricFacet P F := by
  constructor
  · intro hF
    refine ⟨hF.1, hF.2.1, ?_, ?_⟩
    · intro heq
      have hd := hF.2.2
      rw [heq] at hd
      omega
    · intro G hG hFG hGP
      by_contra hGF
      have hlt := face_affineDimension_lt
        (face_restrict hF.1 hG.2.1 hFG) hF.2.1 (Ne.symm hGF)
      have hlt' := face_affineDimension_lt hG (hF.2.1.mono hFG) hGP
      have hd := hF.2.2
      omega
  · intro hF
    obtain ⟨G, hG, hFG⟩ := finitePolytope_face_subset_facet hP hF.1 hF.2.1 hF.2.2.1
    have hGP : G ≠ P := by
      intro heq
      have hd := hG.2.2
      rw [heq] at hd
      omega
    have heq := hF.2.2.2 G hG.1 hFG hGP
    simpa only [heq] using hG

omit [FiniteDimensional ℝ E] in
theorem vertexTransitive_iff_extremePoints {P : Set E} (hP : FinitePolytope P) :
    VertexTransitive P ↔ IsVertexTransitive (P.extremePoints ℝ) := by
  constructor
  · intro h v hv w hw
    obtain ⟨g, hg, hgw⟩ := h v hv w hw
    refine ⟨g, ?_, hgw⟩
    rw [affineIsometry_image_extremePoints, hg]
  · intro h v hv w hw
    obtain ⟨g, hg, hgw⟩ := h v hv w hw
    refine ⟨g, ?_, hgw⟩
    calc
      g '' P = g '' convexHull ℝ (P.extremePoints ℝ) := by
        rw [← finitePolytope_eq_convexHull_extremePoints hP]
      _ = convexHull ℝ (g '' P.extremePoints ℝ) := g.toAffineMap.image_convexHull _
      _ = P := by rw [hg, ← finitePolytope_eq_convexHull_extremePoints hP]

theorem edge_iff_geometricEdge {P : Set E} (hP : FinitePolytope P) (v w : E) :
    Edge P v w ↔ GeometricEdge (P.extremePoints ℝ) v w := by
  rw [GeometricEdge, ← finitePolytope_eq_convexHull_extremePoints hP]
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, convex_segment v w, h.2.2.2.isExtreme⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, finitePolytope_face_isExposed hP h.2.2.2⟩

theorem unitEdges_iff_geometricEdges {P : Set E} (hP : FinitePolytope P) :
    UnitEdges P ↔ ∀ v w, GeometricEdge (P.extremePoints ℝ) v w → dist v w = 1 := by
  simp only [UnitEdges, ← edge_iff_geometricEdge hP]

/-- A star expressed as facet vertex sets is exactly the image of the
star expressed as actual convex facets. The root is an actual vertex. -/
theorem facetStar_vertices_image {P : Set E} (hP : FinitePolytope P)
    {v : E} (hv : v ∈ P.extremePoints ℝ) :
    Uniform5.facetStar (P.extremePoints ℝ) v =
      (fun F => P.extremePoints ℝ ∩ F) '' facetStar P v := by
  ext W
  constructor
  · rintro ⟨F, hF, rfl, hvF⟩
    rw [← finitePolytope_eq_convexHull_extremePoints hP] at hF
    exact ⟨F, ⟨(facet_iff_isGeometricFacet hP).mpr hF, hvF.2⟩, rfl⟩
  · rintro ⟨F, ⟨hF, hvF⟩, rfl⟩
    refine ⟨F, ?_, rfl, hv, hvF⟩
    rw [← finitePolytope_eq_convexHull_extremePoints hP]
    exact (facet_iff_isGeometricFacet hP).mp hF

/-- Taking convex hulls is the inverse conversion of star encodings. -/
theorem facetStar_hulls_image {P : Set E} (hP : FinitePolytope P)
    {v : E} (hv : v ∈ P.extremePoints ℝ) :
    convexHull ℝ '' Uniform5.facetStar (P.extremePoints ℝ) v = facetStar P v := by
  rw [facetStar_vertices_image hP hv]
  ext F
  constructor
  · rintro ⟨W, ⟨G, hG, rfl⟩, rfl⟩
    rw [← face_eq_convexHull_vertices hP hG.1.1]
    exact hG
  · intro hF
    refine ⟨P.extremePoints ℝ ∩ F, ⟨F, hF, rfl⟩, ?_⟩
    exact (face_eq_convexHull_vertices hP hF.1.1).symm

omit [FiniteDimensional ℝ E] in
/-- The vertex-set conversion loses no facet information. -/
theorem facetStar_vertices_injective {P : Set E} (hP : FinitePolytope P) (v : E) :
    Set.InjOn (fun F => P.extremePoints ℝ ∩ F) (facetStar P v) := by
  intro F hF G hG hFG
  exact face_eq_of_vertices_eq hP hF.1.1 hG.1.1 hFG

@[simp] theorem affineDimension_eq_main (P : Set Euclidean5) :
    affineDimension P = Uniform5.affineDimension P := rfl

@[simp] theorem polygonPoint_eq_regularPolygonVertex (n : ℕ) (r : ℝ) (i : Fin n) :
    polygonPoint n r i = regularPolygonVertex n r i := rfl

theorem uniform_two_iff_regularPolygon {P : Set Euclidean5} (hP : FinitePolytope P) :
    Uniform 2 P ↔ RegularPolygon (P.extremePoints ℝ) := by
  rw [Uniform]
  constructor
  · rintro ⟨n, hn, r, hr, f, rfl⟩
    refine ⟨n, hn, r, hr, f, ?_⟩
    rw [← embedding_extremePoints, polygon_extremePoints n r hr.le]
    rw [← Set.range_comp]
    rfl
  · rintro ⟨n, hn, r, hr, f, hf⟩
    refine ⟨n, hn, r, hr, f, ?_⟩
    rw [finitePolytope_eq_convexHull_extremePoints hP, hf, polygon]
    change convexHull ℝ _ = f.toAffineMap '' convexHull ℝ _
    rw [f.toAffineMap.image_convexHull, ← Set.range_comp]
    rfl

private theorem face_vertices_bridge {V P F : Set Euclidean5}
    (hV : P.extremePoints ℝ = V ∩ P) (hF : IsConvexFace P F) :
    F.extremePoints ℝ = V ∩ F := by
  rw [face_extremePoints_eq hF, hV]
  ext x
  constructor
  · rintro ⟨hxF, hxV, _⟩
    exact ⟨hxV, hxF⟩
  · rintro ⟨hxV, hxF⟩
    exact ⟨hxF, hxV, hF.2.1 hxF⟩

/-- The recursive predicates coincide on every finite hull of dimension
at least two, with its actual incident vertices. -/
theorem paperRecursiveUniform_iff_uniform {V P : Set Euclidean5}
    (hP : FinitePolytope P) (hV : P.extremePoints ℝ = V ∩ P)
    (hd : 2 ≤ affineDimension P) :
    PaperRecursiveUniform V P ↔ Uniform (affineDimension P) P := by
  generalize hn : affineDimension P = n at hd ⊢
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases htwo : n = 2
    · rw [htwo] at hn ⊢
      constructor
      · intro h
        cases h with
        | polygon _ hr => exact (uniform_two_iff_regularPolygon hP).mpr (hV.symm ▸ hr)
        | higher hgt _ _ =>
          change 2 < affineDimension P at hgt
          omega
      · intro h
        exact PaperRecursiveUniform.polygon (by simpa only [← affineDimension_eq_main] using hn)
          (hV ▸ (uniform_two_iff_regularPolygon hP).mp h)
    · have hthree : 3 ≤ n := by omega
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have facets (G : Set Euclidean5) (hG : Facet P G) :
          PaperRecursiveUniform V G ↔ Uniform (k + 2) G := by
        have hdim : affineDimension G = k + 2 := by
          have hdim := hG.2.2
          rw [hn] at hdim
          omega
        exact ih (k + 2) (by omega) (finitePolytope_facet hP hG)
          (face_vertices_bridge hV hG.1) hdim (by omega)
      constructor
      · intro h
        cases h with
        | polygon hp _ =>
          change affineDimension P = 2 at hp
          omega
        | higher _ ht hf =>
          rw [Uniform]
          refine ⟨hP, hn, (vertexTransitive_iff_extremePoints hP).mpr (hV.symm ▸ ht), ?_⟩
          intro G hG
          exact (facets G hG).mp (hf G ((facet_iff_isGeometricFacet hP).mp hG))
      · intro h
        rw [Uniform] at h
        apply PaperRecursiveUniform.higher
        · change 2 < affineDimension P
          omega
        · rw [← hV]
          exact (vertexTransitive_iff_extremePoints hP).mp h.2.2.1
        · intro G hG
          have hG' := (facet_iff_isGeometricFacet hP).mpr hG
          exact (facets G hG').mpr (h.2.2.2 G hG')

/-- Construct the vertex-set model directly from the composition theorem's
geometric input. All facewise symmetry data are derived by the main API. -/
noncomputable def toEuclideanPaper5 (P : Set Euclidean5) (hP : UnitUniform 5 P) :
    EuclideanPaper5 := by
  let hp := uniform_finitePolytope hP.1
  have hh : convexHull ℝ (P.extremePoints ℝ) = P :=
    (finitePolytope_eq_convexHull_extremePoints hp).symm
  apply EuclideanPaper5.ofVertices (P.extremePoints ℝ)
    (finitePolytope_extremePoints_finite hp)
  · rw [← affineSpan_convexHull (𝕜 := ℝ), hh]
    exact uniform5_affineSpan_eq_top hP.1
  · intro x hx
    rw [hh]
    exact (singleton_face_iff_extremePoint P x).mpr hx
  · exact (unitEdges_iff_geometricEdges hp).mp hP.2
  · rw [hh]
    have he : P.extremePoints ℝ = P.extremePoints ℝ ∩ P :=
      (inter_eq_left.mpr extremePoints_subset).symm
    have hd : 2 ≤ affineDimension P := by rw [uniform_dimension hP.1]; norm_num
    apply (paperRecursiveUniform_iff_uniform hp he hd).mpr
    rw [uniform_dimension hP.1]
    exact hP.1

@[simp] theorem toEuclideanPaper5_vertices (P : Set Euclidean5) (hP : UnitUniform 5 P) :
    (toEuclideanPaper5 P hP).vertices = P.extremePoints ℝ := rfl

@[simp] theorem toEuclideanPaper5_hull (P : Set Euclidean5) (hP : UnitUniform 5 P) :
    convexHull ℝ (toEuclideanPaper5 P hP).vertices = P :=
  (finitePolytope_eq_convexHull_extremePoints (uniform_finitePolytope hP.1)).symm

/-- Every main paper-class model satisfies the unchanged geometric input
of the classification theorem. -/
theorem euclideanPaper5_unitUniform (Q : EuclideanPaper5) :
    UnitUniform 5 (convexHull ℝ Q.vertices) := by
  have hne : Q.vertices.Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    have hs := Q.spanning
    rw [he, AffineSubspace.span_empty] at hs
    exact bot_ne_top hs
  have hp : FinitePolytope (convexHull ℝ Q.vertices) := by
    refine ⟨Q.finite_vertices.toFinset, Q.finite_vertices.toFinset_nonempty.mpr hne, ?_⟩
    rw [Set.Finite.coe_toFinset]
  have hv : (convexHull ℝ Q.vertices).extremePoints ℝ = Q.vertices :=
    Q.toEuclideanUniform5.vertices_eq_extremePoints.symm
  have hd : affineDimension (convexHull ℝ Q.vertices) = 5 := by
    change Module.finrank ℝ (affineSpan ℝ (convexHull ℝ Q.vertices)).direction = 5
    rw [affineSpan_convexHull, Q.spanning, AffineSubspace.direction_top]
    simp [Euclidean5]
  constructor
  · have he : (convexHull ℝ Q.vertices).extremePoints ℝ =
        Q.vertices ∩ convexHull ℝ Q.vertices := by
      rw [hv, inter_eq_left.mpr (subset_convexHull ℝ Q.vertices)]
    have hu := (paperRecursiveUniform_iff_uniform hp he (by omega)).mp Q.paper_uniform
    rwa [hd] at hu
  · apply (unitEdges_iff_geometricEdges hp).mpr
    rw [hv]
    exact Q.unit_edges

/-- The classification theorem's five-dimensional inputs and the main
paper-recursive models have exactly the same hulls. -/
theorem unitUniform5_iff_euclideanPaper5 (P : Set Euclidean5) :
    UnitUniform 5 P ↔ ∃ Q : EuclideanPaper5, convexHull ℝ Q.vertices = P := by
  constructor
  · intro hP
    exact ⟨toEuclideanPaper5 P hP, toEuclideanPaper5_hull P hP⟩
  · rintro ⟨Q, rfl⟩
    exact euclideanPaper5_unitUniform Q

/-- The two concrete five-polytope model types are equivalent, including
their actual vertex and hull data. -/
noncomputable def unitUniform5EquivEuclideanPaper5 : UnitUniform5 ≃ EuclideanPaper5 where
  toFun P := toEuclideanPaper5 P.val P.property
  invFun Q := ⟨convexHull ℝ Q.vertices, euclideanPaper5_unitUniform Q⟩
  left_inv P := Subtype.ext (toEuclideanPaper5_hull P.val P.property)
  right_inv Q := EuclideanPaper5.ext Q.toEuclideanUniform5.vertices_eq_extremePoints.symm

end Uniform5.Composition
