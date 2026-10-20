import Uniform5.CompositionCaseBTypeIRadius

/-! Actual parent-center displacement and normalized cell-center rays. -/
noncomputable section
namespace Uniform5.Composition
open Set InnerProductGeometry
open scoped RealInnerProductSpace

noncomputable def polygonParentOffset {P G : Set (Space 5)} (hP : UnitUniform 5 P)
    {n : ℕ} (hG : PolygonFace P G n) : Space 5 :=
  vertexCentroid (vertices P (uniform_finitePolytope hP.1)) -
    ActualPolygonCycle.polygonCenter hP hG

/-- The normal displacement is the actual Pythagorean complement of the
polygon circumradius in the parent circumradius. -/
theorem polygonParentOffset_norm_sq {P G : Set (Space 5)} (hP : UnitUniform 5 P)
    {n : ℕ} (hG : PolygonFace P G n) :
    ‖polygonParentOffset hP hG‖ ^ 2 = intrinsicRadius P ^ 2 - unitPolygonRadius n ^ 2 := by
  let hPP := uniform_finitePolytope hP.1
  let hGP := finitePolytope_face hPP hG.1 (polygonFace_nonempty hG)
  let o := vertexCentroid (vertices P hPP)
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  obtain ⟨r, hr, hrs, _, _, hoff⟩ :=
    uniform_face_center_projection hP.1 hG.1 (polygonFace_nonempty hG) o (intrinsicRadius P) hs
  have hre : r = unitPolygonRadius n := by
    apply polygonFace_intrinsic_radius hP hG
      (subset_affineSpan ℝ G (intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hGP)))
    intro x hx
    rw [dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hr).mp (hrs x hx)
  have hnorm : ‖polygonParentOffset hP hG‖ = Real.sqrt (intrinsicRadius P ^ 2 - r ^ 2) := by
    simpa only [polygonParentOffset, ActualPolygonCycle.polygonCenter, dist_eq_norm] using hoff
  have hnonneg : 0 ≤ intrinsicRadius P ^ 2 - r ^ 2 := by
    have hproper : G ≠ P := by
      intro he
      have hd := uniform_dimension hP.1
      rw [← he, hG.2.1] at hd
      omega
    have hle := uniform_proper_face_intrinsicRadius_lt hP.1 hG.1
      (polygonFace_nonempty hG) hproper
    have hradius : intrinsicRadius G = r :=
      (show HasIntrinsicRadius G r from ⟨_, hr, hrs⟩).eq_intrinsicRadius.symm
    rw [hradius, hre] at hle
    rw [hre]
    nlinarith [uniform_intrinsicRadius_pos hP.1, unitPolygonRadius_pos (polygonFace_unitPolygon hP hG).1]
  rw [hnorm, Real.sq_sqrt hnonneg, hre]

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

noncomputable def normalizedCellRay (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (i : ℕ) : Space 5 :=
  ‖D.cellCenter hP hG i - polygonCenter hP hG‖⁻¹ •
    (D.cellCenter hP hG i - polygonCenter hP hG)

/-- The actual cell-center ray has the exact projection prescribed by
orthogonal projection of the parent center onto its cell. -/
theorem cellCenterRay_inner_parent (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (i : ℕ) :
    ⟪D.cellCenter hP hG i - polygonCenter hP hG, polygonParentOffset hP hG⟫ =
      ‖D.cellCenter hP hG i - polygonCenter hP hG‖ ^ 2 := by
  let hPP := uniform_finitePolytope hP.1
  let hGne := polygonFace_nonempty hG
  let o := vertexCentroid (vertices P hPP)
  let f := polygonCenter hP hG
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  obtain ⟨_, _, _, hproj, _, _⟩ := uniform_face_center_projection hP.1
    (D.cell_face i) (hGne.mono (D.cell_contains i)) o (intrinsicRadius P) hs
  have hf : f ∈ affineSpan ℝ (D.cell i) := subset_affineSpan ℝ _
    (D.cell_contains i (intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior _)))
  have hh := projection_ray_inner (D.cell i) (hGne.mono (D.cell_contains i)) o f hf
  rw [hproj] at hh
  exact hh

/-- For a prism cell the normalized actual center ray is unit and has
axial projection exactly one half. -/
theorem prism_normalizedCellRay (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (i : ℕ)
    (hi : Congruent (D.cell i) (polygonPrismModel n)) :
    ‖D.normalizedCellRay hP hG i‖ = 1 ∧
      ⟪D.normalizedCellRay hP hG i, polygonParentOffset hP hG⟫ = 1 / 2 := by
  have hn : ‖D.cellCenter hP hG i - polygonCenter hP hG‖ = 1 / 2 := by
    rw [← D.height_eq hP hG]
    exact D.prism_height hP hG i hi
  constructor
  · exact normalized_center_unit rfl (by rw [hn]; norm_num)
  · rw [normalizedCellRay, real_inner_smul_left, D.cellCenterRay_inner_parent hP hG, hn]
    norm_num

end ActualPolygonCycle
end Uniform5.Composition
