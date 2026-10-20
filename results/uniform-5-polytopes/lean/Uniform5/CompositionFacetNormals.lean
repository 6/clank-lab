import Uniform5.CompositionFaceCenters
import Uniform5.CompositionDimension

/-! Supporting hyperplanes and outward facet normals from actual geometry. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A nonzero normal orthogonal to a codimension-one face determines its
whole affine hyperplane, not just a containing hyperplane. -/
theorem affineSpan_eq_normal_hyperplane {F : Set E} {a n : E}
    (ha : a ∈ affineSpan ℝ F) (hn : n ≠ 0)
    (hd : affineDimension F + 1 = Module.finrank ℝ E)
    (ho : n ∈ (affineSpan ℝ F).directionᗮ) :
    (affineSpan ℝ F : Set E) = {x | inner n (x - a) = (0 : ℝ)} := by
  let L : E →ₗ[ℝ] ℝ := (innerSL ℝ n).toLinearMap
  have hL : L ≠ 0 := by
    intro hh
    have hnn := LinearMap.congr_fun hh n
    change inner n n = (0 : ℝ) at hnn
    exact hn (inner_self_eq_zero.mp hnn)
  have hle : (affineSpan ℝ F).direction ≤ LinearMap.ker L := by
    intro x hx
    exact ((Submodule.mem_orthogonal' _ _).mp ho) x hx
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hL
  have hdir : (affineSpan ℝ F).direction = LinearMap.ker L :=
    Submodule.eq_of_le_of_finrank_eq hle (by unfold affineDimension Uniform5.affineDimension at hd; omega)
  ext x
  have hm := AffineSubspace.vadd_mem_iff_mem_direction (x - a) ha
  simpa only [vadd_eq_add, sub_add_cancel, hdir, LinearMap.mem_ker,
    Set.mem_setOf_eq] using hm

/-- If a proper exposed face spans a hyperplane, the vector from an
interior-side point to its orthogonal projection is an outward normal. -/
theorem face_outward_normal {P F : Set E} (hP : FinitePolytope P)
    (hF : IsConvexFace P F) {c a : E} (hc : c ∈ P) (hcF : c ∉ F)
    (ha : a ∈ F)
    (hplane : (affineSpan ℝ F : Set E) =
      {x | inner (a - c) (x - a) = (0 : ℝ)}) :
    ∀ x ∈ P, inner (a - c) (x - a) ≤ (0 : ℝ) := by
  obtain ⟨L, hL⟩ := finitePolytope_face_isExposed hP hF ⟨a, ha⟩
  have hmax := (Set.ext_iff.mp hL a).mp ha
  have hstrict : L c < L a := by
    refine lt_of_le_of_ne (hmax.2 c hc) ?_
    intro hh
    apply hcF
    rw [hL]
    exact ⟨hc, fun y hy => (hmax.2 y hy).trans_eq hh.symm⟩
  have hlevel : ∀ y ∈ F, L y = L a := by
    intro y hy
    have hh := (Set.ext_iff.mp hL y).mp hy
    exact le_antisymm (hmax.2 y (hF.2.1 hy)) (hh.2 a (hF.2.1 ha))
  have hker : (affineSpan ℝ F).direction ≤ LinearMap.ker L.toLinearMap := by
    rw [direction_affineSpan]
    exact vectorSpan_le_ker_of_level L.toLinearMap F (L a) hlevel
  have hn : a - c ≠ 0 := by
    intro hz
    have hh : a = c := sub_eq_zero.mp hz
    exact hcF (hh ▸ ha)
  have hnn : (0 : ℝ) < inner (a - c) (a - c) := real_inner_self_pos.mpr hn
  have hLn : 0 < L (a - c) := by rw [map_sub]; exact sub_pos.mpr hstrict
  intro x hx
  let t : ℝ := inner (a - c) (x - a) / inner (a - c) (a - c)
  let y := (x - a) - t • (a - c)
  have hy : y ∈ (affineSpan ℝ F).direction := by
    have haa := subset_affineSpan ℝ F ha
    have hm := AffineSubspace.vadd_mem_iff_mem_direction y haa
    apply hm.mp
    change y + a ∈ (affineSpan ℝ F : Set E)
    rw [hplane]
    change inner (a - c) (y + a - a) = (0 : ℝ)
    simp only [add_sub_cancel_right]
    dsimp [y, t]
    rw [inner_sub_right, inner_smul_right]
    rw [div_mul_cancel₀ _ hnn.ne']
    exact sub_self _
  have hLy : L y = 0 := hker hy
  have hbound := hmax.2 x hx
  have hteq : L x - L a = t * L (a - c) := by
    dsimp [y] at hLy
    rw [map_sub, map_sub, map_smul] at hLy
    change L x - L a - t * L (a - c) = 0 at hLy
    linarith
  have ht : t ≤ 0 := by nlinarith
  have hh := (div_le_iff₀ hnn).mp ht
  simpa only [zero_mul] using hh

/-- Uniform facets have actual outward normal `a-c`, where `a` and `c`
are their respective vertex centroids. The full-span hypothesis merely
identifies the ambient dimension; it is automatic for `Space (n+3)`. -/
theorem uniform_facet_hyperplane_and_support {n : ℕ} {P F : Set E}
    (hP : Uniform (n + 3) P) (hF : Facet P F)
    (hfull : affineDimension P = Module.finrank ℝ E) :
    let hFP := finitePolytope_face (uniform_finitePolytope hP) hF.1 hF.2.1
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP))
    let a := vertexCentroid (vertices F hFP)
    a ≠ c ∧
      (affineSpan ℝ F : Set E) = {x | inner (a - c) (x - a) = (0 : ℝ)} ∧
      ∀ x ∈ P, inner (a - c) (x - a) ≤ (0 : ℝ) := by
  dsimp only
  let hFP := finitePolytope_face (uniform_finitePolytope hP) hF.1 hF.2.1
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP))
  let a := vertexCentroid (vertices F hFP)
  have hproper : F ≠ P := by
    intro hh
    have hd := hF.2.2
    rw [hh] at hd
    omega
  have hcF : c ∉ F := centroid_not_mem_proper_face (uniform_finitePolytope hP) hF.1 hproper
  have ha : a ∈ F := intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hFP)
  have hne : a ≠ c := by intro hh; exact hcF (hh ▸ ha)
  obtain ⟨R, _, hsP⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP) (uniform_vertexTransitive hP)
  obtain ⟨r, _, hsF⟩ := finitePolytope_transitive_cospherical hFP
    (uniform_face_vertexTransitive hP hF.1 hF.2.1)
  have horth := sphere_centers_sub_mem_orthogonal (F.extremePoints ℝ) c a R r
    (fun x hx => hsP x (hF.1.2.extremePoints_subset_extremePoints hx)) hsF
  have hspan : affineSpan ℝ (F.extremePoints ℝ) = affineSpan ℝ F := by
    rw [← affineSpan_convexHull (𝕜 := ℝ), ← finitePolytope_eq_convexHull_extremePoints hFP]
  rw [hspan] at horth
  have horth' : a - c ∈ (affineSpan ℝ F).directionᗮ := by
    simpa only [neg_sub] using (affineSpan ℝ F).directionᗮ.neg_mem horth
  have hp := affineSpan_eq_normal_hyperplane (subset_affineSpan ℝ F ha)
    (sub_ne_zero.mpr hne) (hF.2.2.trans hfull) horth'
  exact ⟨hne, hp, face_outward_normal (uniform_finitePolytope hP) hF.1
    (intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior (uniform_finitePolytope hP)))
    hcF ha hp⟩

end Uniform5.Composition
