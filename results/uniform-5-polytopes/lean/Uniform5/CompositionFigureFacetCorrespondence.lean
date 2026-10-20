import Uniform5.CompositionSimpleVertex
import Uniform5.CompositionFacetFigures

/-! Actual facets of a vertex figure correspond to incident parent facets. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- At an origin vertex the rank-shifting face correspondence gives all
facets, with uniqueness as literal subsets of the parent polytope. -/
theorem finitePolytope_zeroFigure_facet_correspondence {P : Set E}
    (hP : FinitePolytope P) (hz : (0 : E) ∈ P.extremePoints ℝ)
    (c : E) (R : ℝ) (hs : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2)
    (hu : UnitEdges P) (hd : 2 ≤ affineDimension P) :
    (∀ F, Facet P F → (0 : E) ∈ F →
      Facet (vertexFigure P 0 c) (F ∩ vertexFigure P 0 c)) ∧
    (∀ G, Facet (vertexFigure P 0 c) G →
      ∃! F, Facet P F ∧ (0 : E) ∈ F ∧ F ∩ vertexFigure P 0 c = G) := by
  let V := vertices P hP
  have hzero : 0 ∈ V := (mem_vertices hP 0).mpr hz
  have hheight := (cosphericalUnit_simpleVertex_heights V hzero c R
    (fun x hx => hs x ((mem_vertices hP x).mp hx))
    (fun x y hxy => hu x y ((edge_iff_vertices_isEdge hP x y).mpr hxy))).1
  have hHull : convexHull ℝ (V : Set E) = P := convexHull_vertices hP
  have hQ : heightSection (convexHull ℝ (V : Set E)) (sphereHeight c) =
      vertexFigure P 0 c := by simp only [heightSection, vertexFigure, hHull, sub_zero]
  constructor
  · intro F hF hzF
    have hh := apexFacet_section_facet V hzero (sphereHeight c) hheight
      (hHull.symm ▸ hd) (hHull.symm ▸ hF) hzF
    simpa only [hQ] using hh
  · intro G hG
    have hG' : Facet (heightSection (convexHull ℝ (V : Set E)) (sphereHeight c)) G :=
      hQ.symm ▸ hG
    let F := sectionFaceLift (convexHull ℝ (V : Set E)) (sphereHeight c) G
    have hF : Facet P F := hHull ▸ sectionFacet_lift_facet V hzero _ hheight hG'
    have hzF : (0 : E) ∈ F := ⟨hHull.symm ▸ hz.1, Or.inl rfl⟩
    have hFG : F ∩ vertexFigure P 0 c = G := by
      rw [← hQ]
      exact sectionFaceLift_section _ hG'.1.2.1
    refine ⟨F, ⟨hF, hzF, hFG⟩, ?_⟩
    rintro F' ⟨hF', hzF', hFG'⟩
    apply apexFace_eq_of_section_eq V (sphereHeight c) hheight
      (hHull.symm ▸ hF'.1) (hHull.symm ▸ hF.1) hzF' hzF
    rw [hQ, hFG', hFG]

/-- The facet correspondence at every actual vertex. All cutting-height
conditions are consequences of the sphere and unit edges. -/
theorem finitePolytope_vertexFigure_facet_correspondence {P : Set E}
    (hP : FinitePolytope P) {v : E} (hv : v ∈ P.extremePoints ℝ)
    (c : E) (R : ℝ) (hs : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2)
    (hu : UnitEdges P) (hd : 2 ≤ affineDimension P) :
    (∀ F, Facet P F → v ∈ F →
      Facet (vertexFigure P v c) (F ∩ vertexFigure P v c)) ∧
    (∀ G, Facet (vertexFigure P v c) G →
      ∃! F, Facet P F ∧ v ∈ F ∧ F ∩ vertexFigure P v c = G) := by
  let g := AffineIsometryEquiv.constVAdd ℝ E (-v)
  have hg (x : E) : g x = x - v := by simp [g, sub_eq_add_neg, add_comm]
  have hgv : g v = 0 := by rw [hg, sub_self]
  have hz : (0 : E) ∈ (g '' P).extremePoints ℝ := by
    rw [← affineIsometry_image_extremePoints, ← hgv]
    exact mem_image_of_mem g hv
  have hs' : ∀ x ∈ (g '' P).extremePoints ℝ, ‖x - g c‖ ^ 2 = R ^ 2 := by
    rw [← affineIsometry_image_extremePoints]
    rintro x ⟨y, hy, rfl⟩
    have heq : g y - g c = y - c := by rw [hg, hg]; abel
    rw [heq]
    exact hs y hy
  have hQ : g '' vertexFigure P v c = vertexFigure (g '' P) 0 (g c) := by
    rw [vertexFigure_image, hgv]
  have hcorr := finitePolytope_zeroFigure_facet_correspondence
    (finitePolytope_image g hP) hz (g c) R hs' (unitEdges_image g hu)
    (by simpa only [affineDimension_image] using hd)
  constructor
  · intro F hF hvF
    have hh := hcorr.1 (g '' F) (facet_image g hF)
      (hgv ▸ mem_image_of_mem g hvF)
    apply (facet_image_iff g (vertexFigure P v c) (F ∩ vertexFigure P v c)).mp
    rwa [Set.image_inter g.injective, hQ]
  · intro G hG
    have hG' : Facet (vertexFigure (g '' P) 0 (g c)) (g '' G) :=
      hQ ▸ facet_image g hG
    obtain ⟨F, ⟨hF, hzF, hFG⟩, hunique⟩ := hcorr.2 (g '' G) hG'
    let F' := g.symm '' F
    have hFF : g '' F' = F := by simp only [F', affineIsometry_image_symm_image]
    have hF' : Facet P F' := by
      apply (facet_image_iff g P F').mp
      rwa [hFF]
    have hvF' : v ∈ F' := by
      exact ⟨0, hzF, by rw [← hgv, g.symm_apply_apply]⟩
    have hFG' : F' ∩ vertexFigure P v c = G := by
      apply g.injective.image_injective
      rw [Set.image_inter g.injective, hFF, hQ, hFG]
    refine ⟨F', ⟨hF', hvF', hFG'⟩, ?_⟩
    rintro H ⟨hH, hvH, hHG⟩
    apply g.injective.image_injective
    rw [hFF]
    apply hunique
    refine ⟨facet_image g hH, hgv ▸ mem_image_of_mem g hvH, ?_⟩
    rw [← hQ, ← Set.image_inter g.injective, hHG]

/-- Uniformity discharges the sphere and dimension premises, using the
actual vertex centroid as the common center. -/
theorem unitUniform_vertexFigure_facet_correspondence {n : ℕ} {P : Set E}
    (hP : UnitUniform (n + 3) P) {v : E} (hv : v ∈ P.extremePoints ℝ) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    (∀ F, Facet P F → v ∈ F →
      Facet (vertexFigure P v c) (F ∩ vertexFigure P v c)) ∧
    (∀ G, Facet (vertexFigure P v c) G →
      ∃! F, Facet P F ∧ v ∈ F ∧ F ∩ vertexFigure P v c = G) := by
  dsimp only
  obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP.1) (uniform_vertexTransitive hP.1)
  exact finitePolytope_vertexFigure_facet_correspondence
    (uniform_finitePolytope hP.1) hv _ R hs hP.2
    (by rw [uniform_dimension hP.1]; omega)

/-- Every actual facet of a five-polytope's vertex figure is the vertex
figure of a genuine incident unit-uniform four-dimensional facet, centered
at that facet's own vertex centroid. -/
theorem unitUniform5_vertexFigure_facet {P : Set E} (hP : UnitUniform 5 P)
    {v : E} (hv : v ∈ P.extremePoints ℝ) {G : Set E}
    (hG : Facet (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) G) :
    ∃ F : Set E, ∃ hF : Facet P F,
      UnitUniform 4 F ∧ v ∈ F.extremePoints ℝ ∧
      F ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) = G ∧
      G = vertexFigure F v (vertexCentroid (vertices F
        (finitePolytope_face (uniform_finitePolytope hP.1) hF.1 hF.2.1))) := by
  obtain ⟨F, ⟨hF, hvF, hFG⟩, _⟩ :=
    (unitUniform_vertexFigure_facet_correspondence (n := 2) hP hv).2 G hG
  have hvF' : v ∈ F.extremePoints ℝ := by
    rw [face_extremePoints_eq hF.1]
    exact ⟨hvF, hv⟩
  refine ⟨F, hF, unitUniform_facet (n := 2) hP hF, hvF', hFG, ?_⟩
  rw [← hFG]
  exact uniform_vertexFigure_face_inter (n := 2) hP.1 hF.1 hF.2.1 hvF

end Uniform5.Composition
