import Uniform5.CompositionPolarMetrics
import Uniform5.CompositionPolygonIncidence

/-!
# Closure from actual incident face centers

All metric, height and nondegeneracy inputs are derived from actual faces.
The ordered once-around fan remains the explicit input to this adapter.
-/
noncomputable section
namespace Uniform5.Composition
open Set InnerProductGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- The actual centroid rays of incident proper faces satisfy the literal
closure equation once their tangent fan has been constructed. -/
theorem actual_center_cycle_closure {m k n : ℕ} {P G : Set E}
    (hP : UnitUniform (m + 3) P) (hG : PolygonFace P G k) (hGne : G.Nonempty)
    (hn : 0 < n) (C : ℕ → Set E) (hC : ∀ i, IsConvexFace P (C i))
    (hGC : ∀ i, G ⊆ C i) (hproper : ∀ i, G ≠ C i)
    (hCproper : ∀ i, C i ≠ P) (hcyclic : C n = C 0) :
    let hGP := finitePolytope_face (uniform_finitePolytope hP.1) hG.1 hGne
    let hCP := fun i => finitePolytope_face (uniform_finitePolytope hP.1) (hC i)
      (hGne.mono (hGC i))
    let o := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    let f := vertexCentroid (vertices G hGP)
    let a := fun i => vertexCentroid (vertices (C i) (hCP i))
    let w := ‖o - f‖⁻¹ • (o - f)
    let u := fun i => ‖a i - f‖⁻¹ • (a i - f)
    SphericalFanData n
      (fun i => angle (sphericalTangent w (u i)) (sphericalTangent w (u (i + 1)))) →
    ∃ R : ℝ, 0 < R ∧ (∀ x ∈ P.extremePoints ℝ, ‖x - o‖ ^ 2 = R ^ 2) ∧
      cycleClosureFunction n (unitPolygonRadius k) (fun i => ‖a i - f‖)
        (fun i => angle (a i - f) (a (i + 1) - f)) (1 / R) = 0 := by
  dsimp only
  intro fan
  let hGP := finitePolytope_face (uniform_finitePolytope hP.1) hG.1 hGne
  let hCP := fun i => finitePolytope_face (uniform_finitePolytope hP.1) (hC i)
    (hGne.mono (hGC i))
  let o := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
  let f := vertexCentroid (vertices G hGP)
  let a := fun i => vertexCentroid (vertices (C i) (hCP i))
  let w := ‖o - f‖⁻¹ • (o - f)
  let u := fun i => ‖a i - f‖⁻¹ • (a i - f)
  have hm (i : ℕ) := uniform_nested_face_polar_cosine hP.1 (hC i) hG.1 hGne
    (hGC i) (hproper i)
  have hap (i : ℕ) : 0 < ‖a i - f‖ := (hm i).2.1
  have hop : 0 < ‖o - f‖ := (hm 0).2.2.1
  obtain ⟨R, hR, hsR⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP.1) (uniform_vertexTransitive hP.1)
  have hRp := uniform_sphere_radius_pos hP.1 hR hsR
  obtain ⟨ρ, hρ, hsρ, _, _, hoff⟩ :=
    uniform_face_center_projection hP.1 hG.1 hGne o R hsR
  have hρeq : ρ = unitPolygonRadius k := by
    apply polygonFace_intrinsic_radius hP hG
      (subset_affineSpan ℝ G (intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hGP)))
    intro x hx
    rw [dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hρ).mp (hsρ x hx)
  have hnorm : ‖o - f‖ = Real.sqrt (R ^ 2 - (unitPolygonRadius k) ^ 2) := by
    simpa only [dist_eq_norm, hρeq] using hoff
  have hsq : ‖o - f‖ ^ 2 = R ^ 2 - (unitPolygonRadius k) ^ 2 := by
    rw [hnorm]
    exact Real.sq_sqrt (Real.sqrt_pos.mp (hnorm ▸ hop)).le
  have huw (i : ℕ) : ‖u i‖ = 1 := normalized_center_unit rfl (hap i)
  have hww : ‖w‖ = 1 := normalized_center_unit rfl hop
  have hac : a n = a 0 := by simp only [a, hcyclic]
  have huc : u n = u 0 := by simp only [u, hac]
  have ht (i : ℕ) : sphericalTangent w (u i) ≠ 0 :=
    uniform_nested_face_tangent_ne_zero hP.1 (hC i) (hCproper i) hG.1 hGne
      (hGC i) (hproper i)
  have hp (i : ℕ) : Real.cos (angle (u i) w) = ‖a i - f‖ / ‖o - f‖ := by
    dsimp only [u, w]
    rw [angle_smul_left_of_pos _ _ (inv_pos.mpr (hap i)),
      angle_smul_right_of_pos _ _ (inv_pos.mpr hop)]
    exact (hm i).2.2.2
  have hangle (i : ℕ) : angle (a i - f) (a (i + 1) - f) = angle (u i) (u (i + 1)) := by
    dsimp only [u]
    rw [angle_smul_left_of_pos _ _ (inv_pos.mpr (hap i)),
      angle_smul_right_of_pos _ _ (inv_pos.mpr (hap (i + 1)))]
  exact ⟨R, hRp, hsR, cycleClosureFunction_zero_of_fan hn hww (fun i _ => huw i)
    huc (fun i _ => ht i) fan hRp hop hsq (fun i _ => hp i) (fun i _ => hangle i)⟩

end Uniform5.Composition
