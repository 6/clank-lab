import Uniform5.CompositionFacetCentroidCone
import Uniform5.CompositionAngleSplit
import Uniform5.CompositionPolygonClosure

/-! The paper's word-angle formula for actual uniform four-polytopes. -/
noncomputable section
namespace Uniform5.Composition
open Set InnerProductGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- Compare an enclosing sphere with the actual intrinsic centroid sphere. -/
theorem centroid_offset_of_spheres {G : Set E} (hG : FinitePolytope G)
    (ht : VertexTransitive G) (o : E) (R ρ : ℝ)
    (ho : ∀ x ∈ G.extremePoints ℝ, ‖x - o‖ ^ 2 = R ^ 2)
    (hf : ∀ x ∈ G.extremePoints ℝ,
      ‖x - vertexCentroid (vertices G hG)‖ ^ 2 = ρ ^ 2) :
    ‖o - vertexCentroid (vertices G hG)‖ = Real.sqrt (R ^ 2 - ρ ^ 2) := by
  obtain ⟨r, _, hs, _, _, hd⟩ := transitive_centroid_projection hG ht o R ho
  obtain ⟨x, hx⟩ := finitePolytope_extremePoints_nonempty hG
  have heq : r ^ 2 = ρ ^ 2 := (hs x hx).symm.trans (hf x hx)
  simpa only [heq, dist_eq_norm] using hd

/-- An actual polygon between two actual cells has exactly the angle
specified by the paper's word (K,p,A,B), with actual circumradii. -/
theorem unitUniform4_word_angle {P G A B : Set E} {k : ℕ}
    (hP : UnitUniform 4 P) (hG : PolygonFace P G k)
    (hA : Facet P A) (hB : Facet P B) (hGA : G ⊆ A) (hGB : G ⊆ B) (hAB : A ≠ B) :
    let hPP := uniform_finitePolytope hP.1
    let hGP := finitePolytope_face hPP hG.1 (polygonFace_nonempty hG)
    let o := vertexCentroid (vertices P hPP)
    let f := vertexCentroid (vertices G hGP)
    let a := vertexCentroid (vertices A (finitePolytope_facet hPP hA))
    let b := vertexCentroid (vertices B (finitePolytope_facet hPP hB))
    ∃ R rA rB : ℝ, 0 < R ∧ 0 < rA ∧ 0 < rB ∧
      (∀ x ∈ P.extremePoints ℝ, ‖x - o‖ ^ 2 = R ^ 2) ∧
      (∀ x ∈ A.extremePoints ℝ, ‖x - a‖ ^ 2 = rA ^ 2) ∧
      (∀ x ∈ B.extremePoints ℝ, ‖x - b‖ ^ 2 = rB ^ 2) ∧
      angle (a - f) (b - f) =
        Real.arccos (Real.sqrt ((rA ^ 2 - (unitPolygonRadius k) ^ 2) /
          (R ^ 2 - (unitPolygonRadius k) ^ 2))) +
        Real.arccos (Real.sqrt ((rB ^ 2 - (unitPolygonRadius k) ^ 2) /
          (R ^ 2 - (unitPolygonRadius k) ^ 2))) := by
  dsimp only
  let hPP := uniform_finitePolytope hP.1
  have hGne := polygonFace_nonempty hG
  let hGP := finitePolytope_face hPP hG.1 hGne
  let o := vertexCentroid (vertices P hPP)
  let f := vertexCentroid (vertices G hGP)
  let a := vertexCentroid (vertices A (finitePolytope_facet hPP hA))
  let b := vertexCentroid (vertices B (finitePolytope_facet hPP hB))
  have hdP : affineDimension P = 4 := uniform_dimension hP.1
  have hdA : affineDimension A = 3 := by have hh := hA.2.2; omega
  have hdB : affineDimension B = 3 := by have hh := hB.2.2; omega
  have hproperA : G ≠ A := by intro he; have hh := hG.2.1; rw [he, hdA] at hh; omega
  have hproperB : G ≠ B := by intro he; have hh := hG.2.1; rw [he, hdB] at hh; omega
  obtain ⟨s, t, hs, ht, hcomb⟩ := uniform_fourFace_centroid_positive_combination
    hP.1 hG.1 hGne hG.2.1 (finitePolytope_self_face hPP) hdP hA.1 hB.1
    hGA hGB hA.1.2.1 hB.1.2.1 hdA hdB hAB
  have hmA := uniform_nested_face_polar_cosine hP.1 hA.1 hG.1 hGne hGA hproperA
  have hmB := uniform_nested_face_polar_cosine hP.1 hB.1 hG.1 hGne hGB hproperB
  obtain ⟨R, hR, hsR⟩ := finitePolytope_transitive_cospherical hPP (uniform_vertexTransitive hP.1)
  obtain ⟨rA, hrA, hsA, _, _, _⟩ := uniform_face_center_projection hP.1 hA.1 hA.2.1 o R hsR
  obtain ⟨rB, hrB, hsB, _, _, _⟩ := uniform_face_center_projection hP.1 hB.1 hB.2.1 o R hsR
  obtain ⟨ρ, hρ, hsρ, _, _, _⟩ := uniform_face_center_projection hP.1 hG.1 hGne o R hsR
  have hρeq : ρ = unitPolygonRadius k := by
    apply polygonFace_intrinsic_radius hP hG
      (subset_affineSpan ℝ G (intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hGP)))
    intro x hx
    rw [dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hρ).mp (hsρ x hx)
  rw [hρeq] at hsρ
  have htrans := uniform_face_vertexTransitive hP.1 hG.1 hGne
  have hGAface := face_restrict hG.1 hA.1.2.1 hGA
  have hGBface := face_restrict hG.1 hB.1.2.1 hGB
  have hOf := centroid_offset_of_spheres hGP htrans o R (unitPolygonRadius k)
    (fun x hx => hsR x (hG.1.2.extremePoints_subset_extremePoints hx)) hsρ
  have hAf := centroid_offset_of_spheres hGP htrans a rA (unitPolygonRadius k)
    (fun x hx => hsA x (hGAface.2.extremePoints_subset_extremePoints hx)) hsρ
  have hBf := centroid_offset_of_spheres hGP htrans b rB (unitPolygonRadius k)
    (fun x hx => hsB x (hGBface.2.extremePoints_subset_extremePoints hx)) hsρ
  have hradA : 0 ≤ rA ^ 2 - (unitPolygonRadius k) ^ 2 :=
    (Real.sqrt_pos.mp (hAf ▸ hmA.2.1)).le
  have hradB : 0 ≤ rB ^ 2 - (unitPolygonRadius k) ^ 2 :=
    (Real.sqrt_pos.mp (hBf ▸ hmB.2.1)).le
  refine ⟨R, rA, rB, uniform_sphere_radius_pos hP.1 hR hsR,
    uniform_sphere_radius_pos (uniform_facets hP.1 hA) hrA hsA,
    uniform_sphere_radius_pos (uniform_facets hP.1 hB) hrB hsB, hsR, hsA, hsB, ?_⟩
  apply wedge_angle_from_radii (norm_pos_iff.mp hmA.2.1) (norm_pos_iff.mp hmA.2.2.1)
    hs ht hcomb hradA hradB
  · exact hmA.2.2.2.trans (by rw [hAf, hOf])
  · exact hmB.2.2.2.trans (by rw [hBf, hOf])

end Uniform5.Composition
