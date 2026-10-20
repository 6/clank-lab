import Uniform5.CompositionUniformFaces
import Uniform5.CompositionPolygonSymmetry
import Uniform5.CompositionRidges
import Mathlib.Geometry.Euclidean.Projection

/-! Actual face circumcenters and orthogonal projection of a circumsphere center. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two sphere centers for the same point set differ orthogonally to its
affine direction. The two radii need not coincide. -/
theorem sphere_centers_sub_mem_orthogonal (S : Set E) (c a : E) (R r : ℝ)
    (hc : ∀ x ∈ S, ‖x - c‖ ^ 2 = R ^ 2)
    (ha : ∀ x ∈ S, ‖x - a‖ ^ 2 = r ^ 2) :
    c - a ∈ (affineSpan ℝ S).directionᗮ := by
  have hd : (affineSpan ℝ S).direction ≤ LinearMap.ker (innerSL ℝ (c - a)).toLinearMap := by
    rw [direction_affineSpan, vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    change inner (c - a) (x - y) = (0 : ℝ)
    have hxc := hc x hx
    have hyc := hc y hy
    have hxa := ha x hx
    have hya := ha y hy
    simp only [norm_sub_sq_real] at hxc hyc hxa hya
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm x c, real_inner_comm y c,
      real_inner_comm x a, real_inner_comm y a]
    nlinarith
  rw [Submodule.mem_orthogonal']
  intro x hx
  exact hd hx

variable [FiniteDimensional ℝ E]

/-- Orthogonal projection to the actual affine span, with nonemptiness
provided by the geometric set rather than an arbitrary choice of span. -/
noncomputable def spanProjection (P : Set E) (hne : P.Nonempty) (c : E) : E := by
  letI : Nonempty (affineSpan ℝ P) :=
    ⟨⟨hne.choose, subset_affineSpan ℝ P hne.choose_spec⟩⟩
  exact ↑(EuclideanGeometry.orthogonalProjection (affineSpan ℝ P) c)

/-- A sphere center lying in the affine span is the orthogonal projection
of any other center for the same spanning point set. -/
theorem spanProjection_eq_of_sphere_centers (P : Set E) (hne : P.Nonempty)
    (S : Set E) (hspan : affineSpan ℝ S = affineSpan ℝ P)
    (c a : E) (haP : a ∈ affineSpan ℝ P) (R r : ℝ)
    (hc : ∀ x ∈ S, ‖x - c‖ ^ 2 = R ^ 2)
    (ha : ∀ x ∈ S, ‖x - a‖ ^ 2 = r ^ 2) :
    spanProjection P hne c = a := by
  letI : Nonempty (affineSpan ℝ P) := ⟨⟨a, haP⟩⟩
  have ho := sphere_centers_sub_mem_orthogonal S c a R r hc ha
  rw [hspan] at ho
  have hp := EuclideanGeometry.orthogonalProjection_vadd_eq_self haP ho
  have hh := congrArg (fun x : affineSpan ℝ P => (x : E)) hp
  simpa only [vadd_eq_add, sub_add_cancel, Subtype.coe_mk, spanProjection] using hh

/-- A transitive finite polytope's vertex centroid is its intrinsic
circumcenter and the projection of every containing circumsphere center. -/
theorem transitive_centroid_projection {P : Set E} (hP : FinitePolytope P)
    (htrans : VertexTransitive P) (c : E) (R : ℝ)
    (hsphere : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2) :
    ∃ r : ℝ, 0 ≤ r ∧
      (∀ x ∈ P.extremePoints ℝ, ‖x - vertexCentroid (vertices P hP)‖ ^ 2 = r ^ 2) ∧
      spanProjection P (finitePolytope_nonempty hP) c = vertexCentroid (vertices P hP) ∧
      vertexCentroid (vertices P hP) ∈ intrinsicInterior ℝ P ∧
      dist c (vertexCentroid (vertices P hP)) = Real.sqrt (R ^ 2 - r ^ 2) := by
  let a := vertexCentroid (vertices P hP)
  obtain ⟨r, hr, hs⟩ := finitePolytope_transitive_cospherical hP htrans
  have hint := vertexCentroid_mem_intrinsicInterior hP
  have haP : a ∈ P := intrinsicInterior_subset hint
  have haA : a ∈ affineSpan ℝ P := subset_affineSpan ℝ P haP
  have hspan : affineSpan ℝ (P.extremePoints ℝ) = affineSpan ℝ P := by
    calc
      affineSpan ℝ (P.extremePoints ℝ) = affineSpan ℝ (convexHull ℝ (P.extremePoints ℝ)) :=
        (affineSpan_convexHull (𝕜 := ℝ) _).symm
      _ = affineSpan ℝ P := congrArg (affineSpan ℝ) (finitePolytope_eq_convexHull_extremePoints hP).symm
  have hp := spanProjection_eq_of_sphere_centers P (finitePolytope_nonempty hP)
    (P.extremePoints ℝ) hspan c a haA R r hsphere hs
  refine ⟨r, hr, hs, hp, hint, ?_⟩
  obtain ⟨x, hx⟩ := finitePolytope_extremePoints_nonempty hP
  letI : Nonempty (affineSpan ℝ P) := ⟨⟨a, haA⟩⟩
  have hproj : (EuclideanGeometry.orthogonalProjection (affineSpan ℝ P) c : E) = a := hp
  have hpy := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    c (subset_affineSpan ℝ P hx.1)
  rw [hproj] at hpy
  have hsx := hsphere x hx
  have hsax := hs x hx
  have hd : dist c a ^ 2 = R ^ 2 - r ^ 2 := by
    rw [← dist_eq_norm] at hsx hsax
    nlinarith [hpy]
  rw [← hd, Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg]

/-- Every nonempty face has its own genuine transitive
symmetry action, derived by descending through facets. -/
theorem uniform_face_vertexTransitive {n : ℕ} {P F : Set E}
    (hP : Uniform (n + 3) P) (hF : IsConvexFace P F) (hne : F.Nonempty) :
    VertexTransitive F := by
  by_cases hd : affineDimension F ≤ 1
  · exact finitePolytope_low_dimension_vertexTransitive
      (finitePolytope_face (uniform_finitePolytope hP) hF hne) hd
  have hUF := uniform_face hP hF hne (by omega)
  by_cases ht : affineDimension F = 2
  · rw [ht] at hUF
    exact uniform2_vertexTransitive hUF
  have heq : affineDimension F = (affineDimension F - 3) + 3 := by omega
  rw [heq] at hUF
  exact uniform_vertexTransitive hUF

/-- Paper `lem:sphere` for every nonempty actual face:
the ambient center projects to the face's intrinsic centroid/circumcenter,
which is relatively interior, with the stated square-root offset. -/
theorem uniform_face_center_projection {n : ℕ} {P F : Set E}
    (hP : Uniform (n + 3) P) (hF : IsConvexFace P F) (hne : F.Nonempty)
    (c : E) (R : ℝ)
    (hsphere : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2) :
    let hFP := finitePolytope_face (uniform_finitePolytope hP) hF hne
    ∃ r : ℝ, 0 ≤ r ∧
      (∀ x ∈ F.extremePoints ℝ, ‖x - vertexCentroid (vertices F hFP)‖ ^ 2 = r ^ 2) ∧
      spanProjection F (finitePolytope_nonempty hFP) c = vertexCentroid (vertices F hFP) ∧
      vertexCentroid (vertices F hFP) ∈ intrinsicInterior ℝ F ∧
      dist c (vertexCentroid (vertices F hFP)) = Real.sqrt (R ^ 2 - r ^ 2) := by
  apply transitive_centroid_projection
    (finitePolytope_face (uniform_finitePolytope hP) hF hne)
    (uniform_face_vertexTransitive hP hF hne) c R
  intro x hx
  exact hsphere x (hF.2.extremePoints_subset_extremePoints hx)

/-- A proper face cannot contain the arithmetic centroid of all actual
vertices. Exposure and the zero sum of centered vertices prove this without
an additional interior assumption. -/
theorem centroid_not_mem_proper_face {P F : Set E} (hP : FinitePolytope P)
    (hF : IsConvexFace P F) (hproper : F ≠ P) :
    vertexCentroid (vertices P hP) ∉ F := by
  classical
  intro hc
  let V := vertices P hP
  let c := vertexCentroid V
  obtain ⟨L, hL⟩ := finitePolytope_face_isExposed hP hF ⟨c, hc⟩
  have hmax := (Set.ext_iff.mp hL c).mp hc
  have hle : ∀ x ∈ V, L (x - c) ≤ 0 := by
    intro x hx
    rw [map_sub]
    exact sub_nonpos.mpr (hmax.2 x ((mem_vertices hP x).mp hx).1)
  have hsum : ∑ x ∈ V, L (x - c) = 0 := by
    rw [← map_sum, sum_sub_vertexCentroid V (vertices_nonempty hP), map_zero]
  have heq : ∀ x ∈ V, L (x - c) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos hle).mp hsum
  have hVF : (V : Set E) ⊆ F := by
    intro x hx
    rw [hL]
    refine ⟨((mem_vertices hP x).mp hx).1, ?_⟩
    have hh := heq x hx
    rw [map_sub, sub_eq_zero] at hh
    intro y hy
    exact (hmax.2 y hy).trans_eq hh.symm
  have hPF : P ⊆ F := by
    rw [← convexHull_vertices hP]
    exact convexHull_min hVF hF.1
  exact hproper (hF.2.1.antisymm hPF)

/-- The actual vertex centroid lies outside the affine span of every
nonempty proper face. -/
theorem centroid_not_mem_proper_face_span {P F : Set E} (hP : FinitePolytope P)
    (hF : IsConvexFace P F) (hne : F.Nonempty) (hproper : F ≠ P) :
    vertexCentroid (vertices P hP) ∉ affineSpan ℝ F := by
  intro hc
  apply centroid_not_mem_proper_face hP hF hproper
  rw [← face_affineSpan_inter hF hne]
  exact ⟨intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hP), hc⟩

/-- Nonempty proper faces have strictly positive
circumcenter offset and strictly smaller radius than the parent sphere. -/
theorem uniform_proper_face_radius_lt {n : ℕ} {P F : Set E}
    (hP : Uniform (n + 3) P) (hF : IsConvexFace P F) (hne : F.Nonempty)
    (hproper : F ≠ P) (R : ℝ) (hR : 0 ≤ R)
    (hsphere : ∀ x ∈ P.extremePoints ℝ,
      ‖x - vertexCentroid (vertices P (uniform_finitePolytope hP))‖ ^ 2 = R ^ 2) :
    let hFP := finitePolytope_face (uniform_finitePolytope hP) hF hne
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP))
    let a := vertexCentroid (vertices F hFP)
    ∃ r : ℝ, 0 ≤ r ∧ r < R ∧
      (∀ x ∈ F.extremePoints ℝ, ‖x - a‖ ^ 2 = r ^ 2) ∧
      spanProjection F hne c = a ∧ a ∈ intrinsicInterior ℝ F ∧
      0 < dist c a ∧ dist c a = Real.sqrt (R ^ 2 - r ^ 2) := by
  dsimp only
  let hFP := finitePolytope_face (uniform_finitePolytope hP) hF hne
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP))
  let a := vertexCentroid (vertices F hFP)
  obtain ⟨r, hr, hs, hp, ha, heq⟩ := uniform_face_center_projection hP hF hne c R hsphere
  have hca : c ≠ a := by
    intro hh
    apply centroid_not_mem_proper_face (uniform_finitePolytope hP) hF hproper
    change c ∈ F
    rw [hh]
    exact intrinsicInterior_subset ha
  have hdist : 0 < dist c a := dist_pos.mpr hca
  have hsqrt : 0 < Real.sqrt (R ^ 2 - r ^ 2) := heq ▸ hdist
  have hsq : 0 < R ^ 2 - r ^ 2 := Real.sqrt_pos.mp hsqrt
  exact ⟨r, hr, by nlinarith, hs, hp, ha, hdist, heq⟩

end Uniform5.Composition
