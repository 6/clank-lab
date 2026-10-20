import Uniform5.CompositionFigureFacetCorrespondence
import Uniform5.CompositionFacetSystemGeneral
import Uniform5.CompositionRidges

/-! Actual polygon faces through an apex and edges of its vertex figure. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- At an origin apex, every nonempty section face has its unique parent
face, with the precise rank shift. -/
theorem finitePolytope_zeroFigure_face_correspondence {P : Set E}
    (hP : FinitePolytope P) (hz : (0 : E) ∈ P.extremePoints ℝ)
    (c : E) (R : ℝ) (hs : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2)
    (hu : UnitEdges P) (k : ℕ) :
    (∀ F, IsConvexFace P F → (0 : E) ∈ F → affineDimension F = k + 1 →
      IsConvexFace (vertexFigure P 0 c) (F ∩ vertexFigure P 0 c) ∧
      (F ∩ vertexFigure P 0 c).Nonempty ∧ affineDimension (F ∩ vertexFigure P 0 c) = k) ∧
    (∀ G, IsConvexFace (vertexFigure P 0 c) G → G.Nonempty → affineDimension G = k →
      ∃! F, IsConvexFace P F ∧ (0 : E) ∈ F ∧ affineDimension F = k + 1 ∧
        F ∩ vertexFigure P 0 c = G) := by
  let V := vertices P hP
  have hzero : 0 ∈ V := (mem_vertices hP 0).mpr hz
  have hheight := (cosphericalUnit_simpleVertex_heights V hzero c R
    (fun x hx => hs x ((mem_vertices hP x).mp hx))
    (fun x y hxy => hu x y ((edge_iff_vertices_isEdge hP x y).mpr hxy))).1
  have hHull : convexHull ℝ (V : Set E) = P := convexHull_vertices hP
  have hQ : heightSection (convexHull ℝ (V : Set E)) (sphereHeight c) =
      vertexFigure P 0 c := by simp only [heightSection, vertexFigure, hHull, sub_zero]
  constructor
  · intro F hF hzF hdF
    have hne : F ≠ {0} := by intro h; rw [h, affineDimension_singleton] at hdF; omega
    have hF' := hHull.symm ▸ hF
    have hd := apexFace_section_dimension V hzero _ hheight hF' hzF hne
    rw [hQ] at hd
    refine ⟨?_, ?_, by omega⟩
    · rw [← hQ]
      exact face_heightSection (convex_convexHull ℝ _) hF' _
    · rw [← hQ]
      exact (apexFace_section_nonempty_iff V _ hheight hF' hzF).mpr hne
  · intro G hG hne hdG
    have hG' : IsConvexFace (heightSection (convexHull ℝ (V : Set E)) (sphereHeight c)) G :=
      hQ.symm ▸ hG
    let F := sectionFaceLift (convexHull ℝ (V : Set E)) (sphereHeight c) G
    have hF' := sectionFaceLift_isFace V hzero _ hheight hG'
    have hF : IsConvexFace P F := hHull ▸ hF'
    have hzF : (0 : E) ∈ F := ⟨hHull.symm ▸ hz.1, Or.inl rfl⟩
    have hFG : F ∩ vertexFigure P 0 c = G := by
      rw [← hQ]
      exact sectionFaceLift_section _ hG'.2.1
    have hFne : F ≠ {0} := by
      apply (apexFace_section_nonempty_iff V _ hheight hF' hzF).mp
      rwa [hQ, hFG]
    have hdF := apexFace_section_dimension V hzero _ hheight hF' hzF hFne
    rw [hQ, hFG, hdG] at hdF
    refine ⟨F, ⟨hF, hzF, hdF.symm, hFG⟩, ?_⟩
    rintro F' ⟨hF'', hzF', _, hFG'⟩
    apply apexFace_eq_of_section_eq V (sphereHeight c) hheight
      (hHull.symm ▸ hF'') (hHull.symm ▸ hF) hzF' hzF
    rw [hQ, hFG', hFG]

/-- The genuine face-rank correspondence is independent of the apex's
coordinates. It includes every nonempty section face, not assumed labels. -/
theorem finitePolytope_vertexFigure_face_correspondence {P : Set E}
    (hP : FinitePolytope P) {v : E} (hv : v ∈ P.extremePoints ℝ)
    (c : E) (R : ℝ) (hs : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2)
    (hu : UnitEdges P) (k : ℕ) :
    (∀ F, IsConvexFace P F → v ∈ F → affineDimension F = k + 1 →
      IsConvexFace (vertexFigure P v c) (F ∩ vertexFigure P v c) ∧
      (F ∩ vertexFigure P v c).Nonempty ∧ affineDimension (F ∩ vertexFigure P v c) = k) ∧
    (∀ G, IsConvexFace (vertexFigure P v c) G → G.Nonempty → affineDimension G = k →
      ∃! F, IsConvexFace P F ∧ v ∈ F ∧ affineDimension F = k + 1 ∧
        F ∩ vertexFigure P v c = G) := by
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
  have hcorr := finitePolytope_zeroFigure_face_correspondence
    (finitePolytope_image g hP) hz (g c) R hs' (unitEdges_image g hu) k
  constructor
  · intro F hF hvF hdF
    obtain ⟨hh, hn, hd⟩ := hcorr.1 (g '' F) (isConvexFace_image g hF)
      (hgv ▸ mem_image_of_mem g hvF) (by rwa [affineDimension_image])
    have hinter : (g '' F) ∩ vertexFigure (g '' P) 0 (g c) =
        g '' (F ∩ vertexFigure P v c) := by rw [Set.image_inter g.injective, hQ]
    rw [hinter] at hh hn hd
    rw [← hQ] at hh
    refine ⟨?_, Set.image_nonempty.mp hn, ?_⟩
    · simpa only [affineIsometry_symm_image_image] using isConvexFace_image g.symm hh
    · simpa only [affineDimension_image] using hd
  · intro G hG hn hdG
    have hG' : IsConvexFace (vertexFigure (g '' P) 0 (g c)) (g '' G) :=
      hQ ▸ isConvexFace_image g hG
    obtain ⟨F, ⟨hF, hzF, hdF, hFG⟩, hunique⟩ := hcorr.2 (g '' G) hG' (hn.image g)
      (by rwa [affineDimension_image])
    let F' := g.symm '' F
    have hFF : g '' F' = F := by simp only [F', affineIsometry_image_symm_image]
    have hF' : IsConvexFace P F' := by
      simpa only [affineIsometry_symm_image_image] using isConvexFace_image g.symm hF
    have hvF' : v ∈ F' := ⟨0, hzF, by rw [← hgv, g.symm_apply_apply]⟩
    have hdF' : affineDimension F' = k + 1 := by
      change affineDimension (g.symm '' F) = _
      rwa [affineDimension_image]
    have hFG' : F' ∩ vertexFigure P v c = G := by
      apply g.injective.image_injective
      rw [Set.image_inter g.injective, hFF, hQ, hFG]
    refine ⟨F', ⟨hF', hvF', hdF', hFG'⟩, ?_⟩
    rintro H ⟨hH, hvH, hdH, hHG⟩
    apply g.injective.image_injective
    rw [hFF]
    apply hunique
    refine ⟨isConvexFace_image g hH, hgv ▸ mem_image_of_mem g hvH,
      by rwa [affineDimension_image], ?_⟩
    rw [← hQ, ← Set.image_inter g.injective, hHG]

/-- A nonempty one-dimensional face of an actual finite polytope is a
true exposed edge with its actual extreme endpoints. -/
theorem finitePolytope_oneFace_edge {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) (hne : G.Nonempty) (hd : affineDimension G = 1) :
    ∃ x y, Edge P x y ∧ G = segment ℝ x y := by
  obtain ⟨x, y, hxy, hseg, hext⟩ :=
    finitePolytope_dim_one_segment (finitePolytope_face hP hG hne) hd
  refine ⟨x, y, ⟨?_, ?_, hxy, ?_⟩, hseg⟩
  · exact hG.2.extremePoints_subset_extremePoints (by rw [hext]; simp)
  · exact hG.2.extremePoints_subset_extremePoints (by rw [hext]; simp)
  · rw [← hseg]
    exact finitePolytope_face_isExposed hP hG

/-- The centroid gives the actual rank-shifting correspondence for every
unit-uniform polytope, without separately assumed section geometry. -/
theorem unitUniform_vertexFigure_face_correspondence {n : ℕ} {P : Set E}
    (hP : UnitUniform (n + 3) P) {v : E} (hv : v ∈ P.extremePoints ℝ) (k : ℕ) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    (∀ F, IsConvexFace P F → v ∈ F → affineDimension F = k + 1 →
      IsConvexFace (vertexFigure P v c) (F ∩ vertexFigure P v c) ∧
      (F ∩ vertexFigure P v c).Nonempty ∧ affineDimension (F ∩ vertexFigure P v c) = k) ∧
    (∀ G, IsConvexFace (vertexFigure P v c) G → G.Nonempty → affineDimension G = k →
      ∃! F, IsConvexFace P F ∧ v ∈ F ∧ affineDimension F = k + 1 ∧
        F ∩ vertexFigure P v c = G) := by
  dsimp only
  obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP.1) (uniform_vertexTransitive hP.1)
  exact finitePolytope_vertexFigure_face_correspondence
    (uniform_finitePolytope hP.1) hv _ R hs hP.2 k

/-- An actual vertex-figure edge comes from exactly one actual two-face
through the distinguished vertex. Uniqueness is equality of subsets. -/
theorem unitUniform5_vertexFigure_edge_unique_twoFace {P : Set E}
    (hP : UnitUniform 5 P) {v : E} (hv : v ∈ P.extremePoints ℝ) {x y : E}
    (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y) :
    ∃! F, IsConvexFace P F ∧ v ∈ F ∧ affineDimension F = 2 ∧
      F ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) =
        segment ℝ x y := by
  exact (unitUniform_vertexFigure_face_correspondence (n := 2) hP hv 1).2 _
    (edge_isConvexFace he) ⟨x, left_mem_segment ℝ x y⟩ (edge_dimension he)

/-- The endpoints of an actual vertex-figure edge are exactly two distinct
actual neighbors of the apex in its polygon face. This is the geometric
input to the regular-polygon chord formula. -/
theorem unitUniform5_vertexFigure_edge_polygon {P : Set E}
    (hP : UnitUniform 5 P) {v : E} (hv : v ∈ P.extremePoints ℝ) {x y : E}
    (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y) :
    ∃ F : Set E, ∃ k : ℕ, PolygonFace P F k ∧ v ∈ F ∧
      Edge F v x ∧ Edge F v y ∧ x ≠ y ∧
      F ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) =
        segment ℝ x y := by
  obtain ⟨F, ⟨hF, hvF, hdF, hFG⟩, _⟩ := unitUniform5_vertexFigure_edge_unique_twoFace hP hv he
  have hFP := finitePolytope_face (uniform_finitePolytope hP.1) hF ⟨v, hvF⟩
  have hxF : x ∈ F := (hFG.symm ▸ left_mem_segment ℝ x y).1
  have hyF : y ∈ F := (hFG.symm ▸ right_mem_segment ℝ x y).1
  obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP.1) (uniform_vertexTransitive hP.1)
  have hext := finitePolytope_unit_vertexFigure_extremePoints
    (uniform_finitePolytope hP.1) hv _ R hs hP.2
  have hvx : Edge P v x := by have hh := he.1; rwa [hext] at hh
  have hvy : Edge P v y := by have hh := he.2.1; rwa [hext] at hh
  refine ⟨F, (vertices F hFP).card, ⟨hF, hdF, vertices F hFP, coe_vertices F hFP, rfl⟩,
    hvF, (edge_face_iff (uniform_finitePolytope hP.1) hF hvF hxF).mp hvx,
    (edge_face_iff (uniform_finitePolytope hP.1) hF hvF hyF).mp hvy, he.2.2.1, hFG⟩

/-- Conversely, each actual polygon face through the apex cuts out an
actual exposed edge of its vertex figure. The endpoints are actual polygon
neighbors, not arbitrarily chosen points of the section. -/
theorem unitUniform5_polygon_vertexFigure_edge {P F : Set E}
    (hP : UnitUniform 5 P) {v : E} (hv : v ∈ P.extremePoints ℝ)
    {k : ℕ} (hF : PolygonFace P F k) (hvF : v ∈ F) :
    ∃ x y, Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y ∧
      Edge F v x ∧ Edge F v y ∧
      F ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) =
        segment ℝ x y := by
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
  obtain ⟨hface, hne, hd⟩ :=
    (unitUniform_vertexFigure_face_correspondence (n := 2) hP hv 1).1 F hF.1 hvF hF.2.1
  obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP.1) (uniform_vertexTransitive hP.1)
  have hQ := finitePolytope_vertexFigure_of_positiveDimension
    (uniform_finitePolytope hP.1) hv c R hs hP.2 (by rw [uniform_dimension hP.1]; norm_num)
  obtain ⟨x, y, he, hseg⟩ := finitePolytope_oneFace_edge hQ hface hne hd
  have hxF : x ∈ F := (hseg.symm ▸ left_mem_segment ℝ x y).1
  have hyF : y ∈ F := (hseg.symm ▸ right_mem_segment ℝ x y).1
  have hext := finitePolytope_unit_vertexFigure_extremePoints
    (uniform_finitePolytope hP.1) hv c R hs hP.2
  have hvx : Edge P v x := by have hh := he.1; rwa [hext] at hh
  have hvy : Edge P v y := by have hh := he.2.1; rwa [hext] at hh
  exact ⟨x, y, he, (edge_face_iff (uniform_finitePolytope hP.1) hF.1 hvF hxF).mp hvx,
    (edge_face_iff (uniform_finitePolytope hP.1) hF.1 hvF hyF).mp hvy, hseg⟩

end Uniform5.Composition
