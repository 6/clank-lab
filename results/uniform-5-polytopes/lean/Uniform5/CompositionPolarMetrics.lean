import Uniform5.CompositionRidgeTangents
import Uniform5.CompositionClosureFunction

/-!
# Actual center offsets and polar angles

The cell-ray projection identity is derived from the actual face centers.
This supplies the metric input of closure; the ordered spherical fan is a
separate geometric construction.
-/
noncomputable section
namespace Uniform5.Composition
open Set InnerProductGeometry
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- Projection onto a cell's span gives the exact inner product of its
center ray with the parent center ray, at any base point in that span. -/
theorem projection_ray_inner (C : Set E) (hne : C.Nonempty) (o f : E)
    (hf : f ∈ affineSpan ℝ C) :
    ⟪spanProjection C hne o - f, o - f⟫ = ‖spanProjection C hne o - f‖ ^ 2 := by
  let a := spanProjection C hne o
  have ha : a ∈ affineSpan ℝ C := spanProjection_mem C hne o
  have had : a - f ∈ (affineSpan ℝ C).direction :=
    AffineSubspace.vsub_mem_direction ha hf
  have ho := spanProjection_sub_mem_orthogonal C hne o
  have hi : ⟪a - f, a - o⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal had ho
  have heq : o - f = (a - f) - (a - o) := by abel
  change ⟪a - f, o - f⟫ = ‖a - f‖ ^ 2
  rw [heq, inner_sub_right, hi, sub_zero, real_inner_self_eq_norm_sq]

/-- The polar cosine uses the actual lengths of the two center offsets. -/
theorem projection_ray_polar_cosine (C : Set E) (hne : C.Nonempty) (o f : E)
    (hf : f ∈ affineSpan ℝ C) (ha : spanProjection C hne o ≠ f) :
    Real.cos (angle (spanProjection C hne o - f) (o - f)) =
      ‖spanProjection C hne o - f‖ / ‖o - f‖ := by
  rw [cos_angle, projection_ray_inner C hne o f hf, sq]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr ha))

/-- Every actual nested proper face determines a nonzero cell-center ray,
and its polar cosine is forced by the actual projection geometry. -/
theorem uniform_nested_face_polar_cosine {n : ℕ} {P C G : Set E}
    (hP : Uniform (n + 3) P) (hC : IsConvexFace P C)
    (hG : IsConvexFace P G) (hGne : G.Nonempty) (hGC : G ⊆ C) (hproper : G ≠ C) :
    let hCP := finitePolytope_face (uniform_finitePolytope hP) hC (hGne.mono hGC)
    let hGP := finitePolytope_face (uniform_finitePolytope hP) hG hGne
    let o := vertexCentroid (vertices P (uniform_finitePolytope hP))
    let a := vertexCentroid (vertices C hCP)
    let f := vertexCentroid (vertices G hGP)
    a ≠ f ∧ 0 < ‖a - f‖ ∧ 0 < ‖o - f‖ ∧
      Real.cos (angle (a - f) (o - f)) = ‖a - f‖ / ‖o - f‖ := by
  dsimp only
  let hCP := finitePolytope_face (uniform_finitePolytope hP) hC (hGne.mono hGC)
  let hGP := finitePolytope_face (uniform_finitePolytope hP) hG hGne
  let o := vertexCentroid (vertices P (uniform_finitePolytope hP))
  let a := vertexCentroid (vertices C hCP)
  let f := vertexCentroid (vertices G hGP)
  have hfG : f ∈ G := intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hGP)
  have hfC : f ∈ affineSpan ℝ C := subset_affineSpan ℝ C (hGC hfG)
  have hGCface : IsConvexFace C G := face_restrict hG hC.2.1 hGC
  have haf : a ≠ f := by
    intro heq
    apply centroid_not_mem_proper_face hCP hGCface hproper
    change a ∈ G
    rw [heq]
    exact hfG
  obtain ⟨R, hR, hRs⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP) (uniform_vertexTransitive hP)
  obtain ⟨_, _, _, hproj, _, _⟩ :=
    uniform_face_center_projection hP hC (hGne.mono hGC) o R hRs
  have hp : spanProjection C (hGne.mono hGC) o = a := hproj
  have hi : ⟪a - f, o - f⟫ = ‖a - f‖ ^ 2 := by
    simpa only [hp] using projection_ray_inner C (hGne.mono hGC) o f hfC
  have hapos : 0 < ‖a - f‖ := norm_pos_iff.mpr (sub_ne_zero.mpr haf)
  have hopos : 0 < ‖o - f‖ := by
    apply norm_pos_iff.mpr
    intro hz
    rw [hz, inner_zero_right] at hi
    nlinarith [sq_pos_of_pos hapos]
  refine ⟨haf, hapos, hopos, ?_⟩
  simpa only [hp] using projection_ray_polar_cosine C (hGne.mono hGC) o f hfC
    (by simpa only [hp] using haf)

omit [FiniteDimensional ℝ E] in
/-- A ray in a subspace cannot have zero tangent about a pole outside that
subspace. Normalization changes neither membership nor direction. -/
theorem normalized_ray_tangent_ne_zero (S : Submodule ℝ E) {u w : E}
    (huS : u ∈ S) (hwS : w ∉ S) (hu : 0 < ‖u‖) (hw : 0 < ‖w‖) :
    sphericalTangent (‖w‖⁻¹ • w) (‖u‖⁻¹ • u) ≠ 0 := by
  intro hz
  let un := ‖u‖⁻¹ • u
  let wn := ‖w‖⁻¹ • w
  have hun : ‖un‖ = 1 := normalized_center_unit rfl hu
  have heq : un = ⟪un, wn⟫ • wn := sub_eq_zero.mp hz
  have hc : ⟪un, wn⟫ ≠ 0 := by
    intro hc
    rw [hc, zero_smul] at heq
    rw [heq, norm_zero] at hun
    norm_num at hun
  have hunS : un ∈ S := S.smul_mem _ huS
  have hwnS : wn ∈ S := (S.smul_mem_iff hc).mp (heq ▸ hunS)
  exact hwS ((S.smul_mem_iff (inv_ne_zero (ne_of_gt hw))).mp hwnS)

/-- Actual proper cell and polygon faces give nonzero spherical tangents;
the parent centroid cannot lie in a proper cell's affine span. -/
theorem uniform_nested_face_tangent_ne_zero {n : ℕ} {P C G : Set E}
    (hP : Uniform (n + 3) P) (hC : IsConvexFace P C) (hCproper : C ≠ P)
    (hG : IsConvexFace P G) (hGne : G.Nonempty) (hGC : G ⊆ C) (hproper : G ≠ C) :
    let hCP := finitePolytope_face (uniform_finitePolytope hP) hC (hGne.mono hGC)
    let hGP := finitePolytope_face (uniform_finitePolytope hP) hG hGne
    let o := vertexCentroid (vertices P (uniform_finitePolytope hP))
    let a := vertexCentroid (vertices C hCP)
    let f := vertexCentroid (vertices G hGP)
    sphericalTangent (‖o - f‖⁻¹ • (o - f)) (‖a - f‖⁻¹ • (a - f)) ≠ 0 := by
  dsimp only
  let hCP := finitePolytope_face (uniform_finitePolytope hP) hC (hGne.mono hGC)
  let hGP := finitePolytope_face (uniform_finitePolytope hP) hG hGne
  let o := vertexCentroid (vertices P (uniform_finitePolytope hP))
  let a := vertexCentroid (vertices C hCP)
  let f := vertexCentroid (vertices G hGP)
  have ha : a ∈ C := intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hCP)
  have hf : f ∈ C := hGC (intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hGP))
  have hu : a - f ∈ (affineSpan ℝ C).direction :=
    AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C ha) (subset_affineSpan ℝ C hf)
  have hw : o - f ∉ (affineSpan ℝ C).direction := by
    intro hw
    apply centroid_not_mem_proper_face_span (uniform_finitePolytope hP) hC
      (hGne.mono hGC) hCproper
    have hh := AffineSubspace.vadd_mem_of_mem_direction hw (subset_affineSpan ℝ C hf)
    simpa only [vadd_eq_add, sub_add_cancel] using hh
  have hm := uniform_nested_face_polar_cosine hP hC hG hGne hGC hproper
  exact normalized_ray_tangent_ne_zero _ hu hw hm.2.1 hm.2.2.1

/-- The square-root polar formula is forced by the actual three spheres.
The radii returned here are certified by the actual vertex sets. -/
theorem uniform_nested_face_radius_cosine {n : ℕ} {P C G : Set E}
    (hP : Uniform (n + 3) P) (hC : IsConvexFace P C)
    (hG : IsConvexFace P G) (hGne : G.Nonempty) (hGC : G ⊆ C) (hproper : G ≠ C) :
    let hCP := finitePolytope_face (uniform_finitePolytope hP) hC (hGne.mono hGC)
    let hGP := finitePolytope_face (uniform_finitePolytope hP) hG hGne
    let o := vertexCentroid (vertices P (uniform_finitePolytope hP))
    let a := vertexCentroid (vertices C hCP)
    let f := vertexCentroid (vertices G hGP)
    ∃ R r ρ : ℝ, 0 ≤ R ∧ 0 ≤ r ∧ 0 ≤ ρ ∧
      (∀ x ∈ P.extremePoints ℝ, ‖x - o‖ ^ 2 = R ^ 2) ∧
      (∀ x ∈ C.extremePoints ℝ, ‖x - a‖ ^ 2 = r ^ 2) ∧
      (∀ x ∈ G.extremePoints ℝ, ‖x - f‖ ^ 2 = ρ ^ 2) ∧
      ‖o - f‖ = Real.sqrt (R ^ 2 - ρ ^ 2) ∧
      ‖a - f‖ = Real.sqrt (r ^ 2 - ρ ^ 2) ∧
      Real.cos (angle (a - f) (o - f)) =
        Real.sqrt (r ^ 2 - ρ ^ 2) / Real.sqrt (R ^ 2 - ρ ^ 2) := by
  dsimp only
  let hCP := finitePolytope_face (uniform_finitePolytope hP) hC (hGne.mono hGC)
  let hGP := finitePolytope_face (uniform_finitePolytope hP) hG hGne
  let o := vertexCentroid (vertices P (uniform_finitePolytope hP))
  let a := vertexCentroid (vertices C hCP)
  let f := vertexCentroid (vertices G hGP)
  obtain ⟨R, hR, hsR⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP) (uniform_vertexTransitive hP)
  obtain ⟨r, hr, hsr, _, _, _⟩ :=
    uniform_face_center_projection hP hC (hGne.mono hGC) o R hsR
  obtain ⟨ρ, hρ, hsρ, _, _, hOf⟩ :=
    uniform_face_center_projection hP hG hGne o R hsR
  have hGCface : IsConvexFace C G := face_restrict hG hC.2.1 hGC
  obtain ⟨ρ', _, hsρ', _, _, hAf⟩ := transitive_centroid_projection hGP
    (uniform_face_vertexTransitive hP hG hGne) a r
    (fun x hx => hsr x (hGCface.2.extremePoints_subset_extremePoints hx))
  obtain ⟨x, hx⟩ := finitePolytope_extremePoints_nonempty hGP
  have heq : ρ' ^ 2 = ρ ^ 2 := (hsρ' x hx).symm.trans (hsρ x hx)
  rw [heq] at hAf
  have hOnorm : ‖o - f‖ = Real.sqrt (R ^ 2 - ρ ^ 2) := by
    simpa only [dist_eq_norm] using hOf
  have hAnorm : ‖a - f‖ = Real.sqrt (r ^ 2 - ρ ^ 2) := by
    simpa only [dist_eq_norm] using hAf
  refine ⟨R, r, ρ, hR, hr, hρ, hsR, hsr, hsρ, hOnorm, hAnorm, ?_⟩
  have hcos := (uniform_nested_face_polar_cosine hP hC hG hGne hGC hproper).2.2.2
  exact hcos.trans (by rw [hOnorm, hAnorm])

/-- The actual parent and cell center rays already lie in the polygon's
orthogonal transverse space, so transverse projection preserves them. -/
theorem uniform_nested_face_rays_mem_orthogonal {n : ℕ} {P C G : Set E}
    (hP : Uniform (n + 3) P) (hC : IsConvexFace P C)
    (hG : IsConvexFace P G) (hGne : G.Nonempty) (hGC : G ⊆ C) :
    let hCP := finitePolytope_face (uniform_finitePolytope hP) hC (hGne.mono hGC)
    let hGP := finitePolytope_face (uniform_finitePolytope hP) hG hGne
    let o := vertexCentroid (vertices P (uniform_finitePolytope hP))
    let a := vertexCentroid (vertices C hCP)
    let f := vertexCentroid (vertices G hGP)
    o - f ∈ (affineSpan ℝ G).directionᗮ ∧ a - f ∈ (affineSpan ℝ G).directionᗮ := by
  dsimp only
  let hCP := finitePolytope_face (uniform_finitePolytope hP) hC (hGne.mono hGC)
  let hGP := finitePolytope_face (uniform_finitePolytope hP) hG hGne
  let o := vertexCentroid (vertices P (uniform_finitePolytope hP))
  let a := vertexCentroid (vertices C hCP)
  let f := vertexCentroid (vertices G hGP)
  obtain ⟨R, _, hsR⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP) (uniform_vertexTransitive hP)
  obtain ⟨r, _, hsr, _, _, _⟩ :=
    uniform_face_center_projection hP hC (hGne.mono hGC) o R hsR
  obtain ⟨_, _, _, hOf, _, _⟩ :=
    uniform_face_center_projection hP hG hGne o R hsR
  have hGCface : IsConvexFace C G := face_restrict hG hC.2.1 hGC
  obtain ⟨_, _, _, hAf, _, _⟩ := transitive_centroid_projection hGP
    (uniform_face_vertexTransitive hP hG hGne) a r
    (fun x hx => hsr x (hGCface.2.extremePoints_subset_extremePoints hx))
  constructor
  · have hh := (affineSpan ℝ G).directionᗮ.neg_mem (spanProjection_sub_mem_orthogonal G hGne o)
    simpa only [hOf, neg_sub] using hh
  · have hh := (affineSpan ℝ G).directionᗮ.neg_mem (spanProjection_sub_mem_orthogonal G hGne a)
    simpa only [hAf, neg_sub] using hh

end Uniform5.Composition
