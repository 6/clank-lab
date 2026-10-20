import Uniform5.CompositionFigureIntrinsic
import Uniform5.CompositionFaceCenters

/-! Actual incident facets and their intrinsic vertex-figure metrics. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Changing the sphere center by a vector perpendicular to a face does
not change the vertex section inside that face. -/
theorem vertexFigure_face_inter_of_orthogonal {P F : Set E}
    (hFP : F ⊆ P) {v c a : E} (hv : v ∈ F)
    (ho : c - a ∈ (affineSpan ℝ F).directionᗮ) :
    F ∩ vertexFigure P v c = vertexFigure F v a := by
  have heq (x : E) (hx : x ∈ F) :
      sphereHeight (c - v) (x - v) = sphereHeight (a - v) (x - v) := by
    have hd := (affineSpan ℝ F).vsub_mem_direction
      (subset_affineSpan ℝ F hx) (subset_affineSpan ℝ F hv)
    have hh := (Submodule.mem_orthogonal' _ _).mp ho (x - v) hd
    change inner (c - a) (x - v) = (0 : ℝ) at hh
    have ha : c - v = (c - a) + (a - v) := by abel
    change (2 : ℝ) * inner (c - v) (x - v) = 2 * inner (a - v) (x - v)
    rw [ha, inner_add_left, hh, zero_add]
  ext x
  simp only [vertexFigure, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxF, _, hx⟩
    exact ⟨hxF, (heq x hxF) ▸ hx⟩
  · rintro ⟨hxF, hx⟩
    exact ⟨hxF, hFP hxF, (heq x hxF).symm ▸ hx⟩

variable [FiniteDimensional ℝ E]

/-- For a face of an actual uniform polytope, section at the parent
centroid equals section at the face's own centroid. -/
theorem uniform_vertexFigure_face_inter {n : ℕ} {P F : Set E}
    (hP : Uniform (n + 3) P) (hF : IsConvexFace P F) (hne : F.Nonempty)
    {v : E} (hv : v ∈ F) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP))
    let hFP := finitePolytope_face (uniform_finitePolytope hP) hF hne
    let a := vertexCentroid (vertices F hFP)
    F ∩ vertexFigure P v c = vertexFigure F v a := by
  dsimp only
  let hFP := finitePolytope_face (uniform_finitePolytope hP) hF hne
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP))
  let a := vertexCentroid (vertices F hFP)
  obtain ⟨R, _, hsP⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP) (uniform_vertexTransitive hP)
  obtain ⟨r, _, hsF⟩ := finitePolytope_transitive_cospherical hFP
    (uniform_face_vertexTransitive hP hF hne)
  have ho := sphere_centers_sub_mem_orthogonal (F.extremePoints ℝ) c a R r
    (fun x hx => hsP x (hF.2.extremePoints_subset_extremePoints hx)) hsF
  have hspan : affineSpan ℝ (F.extremePoints ℝ) = affineSpan ℝ F := by
    rw [← affineSpan_convexHull (𝕜 := ℝ), ← finitePolytope_eq_convexHull_extremePoints hFP]
  rw [hspan] at ho
  exact vertexFigure_face_inter_of_orthogonal hF.2.1 hv ho

/-- Every actual incident facet supplies its intrinsic vertex figure with
its correct center, positive parent radius, relatively interior center,
true vertices and circumradius. In particular this applies to the 3-cells
of a 5-polytope's vertex figure without claiming that figure is uniform. -/
theorem unitUniform_facet_vertexFigure {n : ℕ} {P F : Set E}
    (hP : UnitUniform (n + 4) P) (hF : Facet P F)
    {v : E} (hv : v ∈ F.extremePoints ℝ) :
    let hFP := finitePolytope_face (uniform_finitePolytope hP.1) hF.1 hF.2.1
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    let a := vertexCentroid (vertices F hFP)
    ∃ r : ℝ, 0 < r ∧ (∀ x ∈ F.extremePoints ℝ, dist x a = r) ∧
      F ∩ vertexFigure P v c = vertexFigure F v a ∧
      a + figureCenter (v - a) r ∈ intrinsicInterior ℝ (F ∩ vertexFigure P v c) ∧
      (F ∩ vertexFigure P v c).extremePoints ℝ = {x | Edge F v x} ∧
      ∀ x ∈ (F ∩ vertexFigure P v c).extremePoints ℝ,
        dist x (a + figureCenter (v - a) r) = Real.sqrt (1 - 1 / (4 * r ^ 2)) := by
  dsimp only
  let hFP := finitePolytope_face (uniform_finitePolytope hP.1) hF.1 hF.2.1
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
  let a := vertexCentroid (vertices F hFP)
  have hUF : UnitUniform (n + 3) F := unitUniform_facet hP hF
  obtain ⟨r, hr0, hs⟩ := finitePolytope_transitive_cospherical hFP
    (uniform_vertexTransitive hUF.1)
  have hr : 0 < r := uniform_sphere_radius_pos hUF.1 hr0 hs
  have hsDist : ∀ x ∈ F.extremePoints ℝ, dist x a = r := by
    intro x hx
    rw [dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hr.le).mp (hs x hx)
  have heq := uniform_vertexFigure_face_inter hP.1 hF.1 hF.2.1 hv.1
  have hint := unitUniform_centroid_figureCenter_mem_intrinsicInterior hUF r hr hs hv
  have hvertices := finitePolytope_unit_vertexFigure_extremePoints hFP hv a r hs hUF.2
  refine ⟨r, hr, hsDist, heq, heq.symm ▸ hint, ?_, ?_⟩
  · rw [heq]
    exact hvertices
  · intro x hx
    rw [heq, hvertices] at hx
    exact translated_figure_radius (hsDist x hx.2.1) (hsDist v hv) hr.ne'
      (by rw [dist_comm]; exact hUF.2 v x hx)

/-- The intrinsic center of an incident facet's figure is exactly the
orthogonal projection of the parent figure center. This is the geometric
facet-offset bridge used when applying tangent uniqueness to vertex figures. -/
theorem unitUniform_facet_figureCenter_projection {n : ℕ} {P F : Set E}
    (hP : UnitUniform (n + 4) P) (hF : Facet P F)
    {v : E} (hv : v ∈ F.extremePoints ℝ) (R : ℝ) (hR : 0 < R)
    (hsP : ∀ x ∈ P.extremePoints ℝ,
      dist x (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) = R) :
    let hFP := finitePolytope_face (uniform_finitePolytope hP.1) hF.1 hF.2.1
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    let a := vertexCentroid (vertices F hFP)
    let G := F ∩ vertexFigure P v c
    ∃ r : ℝ, 0 < r ∧ (∀ x ∈ F.extremePoints ℝ, dist x a = r) ∧
      ∃ hne : G.Nonempty,
        spanProjection G hne (c + figureCenter (v - c) R) =
          a + figureCenter (v - a) r ∧
        a + figureCenter (v - a) r ∈ intrinsicInterior ℝ G := by
  dsimp only
  let hFP := finitePolytope_face (uniform_finitePolytope hP.1) hF.1 hF.2.1
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
  let a := vertexCentroid (vertices F hFP)
  let G := F ∩ vertexFigure P v c
  obtain ⟨r, hr, hsF, heq, hint, hext, hrad⟩ := unitUniform_facet_vertexFigure hP hF hv
  let b := a + figureCenter (v - a) r
  have hb : b ∈ G := intrinsicInterior_subset hint
  have hne : G.Nonempty := ⟨b, hb⟩
  refine ⟨r, hr, hsF, hne, ?_, hint⟩
  have hsF2 : ∀ x ∈ F.extremePoints ℝ, ‖x - a‖ ^ 2 = r ^ 2 := by
    intro x hx
    rw [← dist_eq_norm, hsF x hx]
  have hUF : UnitUniform (n + 3) F := unitUniform_facet hP hF
  have hhull := finitePolytope_unit_vertexFigure hFP hv a r hsF2 hUF.2
  have hspan : affineSpan ℝ (G.extremePoints ℝ) = affineSpan ℝ G := by
    change affineSpan ℝ ((F ∩ vertexFigure P v c).extremePoints ℝ) = _
    rw [hext, ← affineSpan_convexHull (𝕜 := ℝ), ← hhull]
    exact congrArg (affineSpan ℝ) heq.symm
  apply spanProjection_eq_of_sphere_centers G hne (G.extremePoints ℝ) hspan
    (c + figureCenter (v - c) R) b (subset_affineSpan ℝ G hb)
    (Real.sqrt (1 - 1 / (4 * R ^ 2))) (Real.sqrt (1 - 1 / (4 * r ^ 2)))
  · intro x hx
    have hxedge : Edge F v x := by rw [hext] at hx; exact hx
    have he : Edge P v x := (edge_face_iff (uniform_finitePolytope hP.1) hF.1 hv.1
      hxedge.2.1.1).mpr hxedge
    have hh := translated_figure_radius (hsP x he.2.1) (hsP v he.1) hR.ne'
      (by rw [dist_comm]; exact hP.2 v x he)
    rw [← dist_eq_norm, hh]
  · intro x hx
    rw [← dist_eq_norm, hrad x hx]

end Uniform5.Composition
