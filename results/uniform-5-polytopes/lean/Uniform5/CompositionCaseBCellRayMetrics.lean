import Uniform5.CompositionCaseBCenterRays

/-! Exact metrics of the actual normalized cell rays in the polygon's
three-dimensional transverse space. -/
noncomputable section
namespace Uniform5.Composition
open Set InnerProductGeometry
open scoped RealInnerProductSpace

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- A cell properly contains the polygon, so its center ray is nonzero. -/
theorem cellCenterRay_norm_pos (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (i : ℕ) :
    0 < ‖D.cellCenter hP hG i - polygonCenter hP hG‖ := by
  have hproper : G ≠ D.cell i := by
    intro he
    have hd := D.cell_dimension i
    rw [← he, hG.2.1] at hd
    omega
  exact (uniform_nested_face_polar_cosine hP.1 (D.cell_face i) hG.1
    (polygonFace_nonempty hG) (D.cell_contains i) hproper).2.1

theorem normalizedCellRay_norm (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (i : ℕ) : ‖D.normalizedCellRay hP hG i‖ = 1 :=
  normalized_center_unit rfl (D.cellCenterRay_norm_pos hP hG i)

/-- Both the parent offset and each normalized cell ray lie in the
orthogonal complement of the actual polygon direction. -/
theorem normalizedCellRay_mem_orthogonal (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (i : ℕ) :
    polygonParentOffset hP hG ∈ (affineSpan ℝ G).directionᗮ ∧
      D.normalizedCellRay hP hG i ∈ (affineSpan ℝ G).directionᗮ := by
  have hh := uniform_nested_face_rays_mem_orthogonal hP.1 (D.cell_face i)
    hG.1 (polygonFace_nonempty hG) (D.cell_contains i)
  exact ⟨hh.1, (affineSpan ℝ G).directionᗮ.smul_mem _ hh.2⟩

/-- Projection onto the cell's affine span determines the actual axial
coordinate of its unit center ray. -/
theorem normalizedCellRay_inner_parent (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (i : ℕ) :
    ⟪D.normalizedCellRay hP hG i, polygonParentOffset hP hG⟫ = D.height n i := by
  rw [normalizedCellRay, real_inner_smul_left, D.cellCenterRay_inner_parent hP hG,
    D.height_eq hP hG]
  have hn := (D.cellCenterRay_norm_pos hP hG i).ne'
  field_simp
  ring

/-- The ray sequence closes at the same actual cell as the incidence cycle. -/
theorem normalizedCellRay_closed (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) :
    D.normalizedCellRay hP hG D.length = D.normalizedCellRay hP hG 0 := by
  simp only [normalizedCellRay, cellCenter, D.cell_closed]

/-- Normalization preserves the actual angle between consecutive cells. -/
theorem normalizedCellRay_angle (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (i : Fin D.length) :
    angle (D.normalizedCellRay hP hG i) (D.normalizedCellRay hP hG (i.val + 1)) =
      D.wordAngle n i := by
  rw [D.wordAngle_eq hP hG i.isLt]
  unfold normalizedCellRay
  rw [angle_smul_left_of_pos _ _ (inv_pos.mpr (D.cellCenterRay_norm_pos hP hG i)),
    angle_smul_right_of_pos _ _ (inv_pos.mpr (D.cellCenterRay_norm_pos hP hG (i.val + 1)))]

/-- The Gram entry is obtained from the actual word angle. -/
theorem normalizedCellRay_inner_next (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (i : Fin D.length) :
    ⟪D.normalizedCellRay hP hG i, D.normalizedCellRay hP hG (i.val + 1)⟫ =
      Real.cos (D.wordAngle n i) := by
  rw [← D.normalizedCellRay_angle hP hG i, cos_angle,
    D.normalizedCellRay_norm hP hG, D.normalizedCellRay_norm hP hG, one_mul, div_one]

/-- The antiprism ray has axial projection half the exact layer separation. -/
theorem antiprism_normalizedCellRay (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (i : ℕ)
    (hi : Congruent (D.cell i) (antiprismModel n)) :
    ‖D.normalizedCellRay hP hG i‖ = 1 ∧
      ⟪D.normalizedCellRay hP hG i, polygonParentOffset hP hG⟫ = antiprismHeight n / 2 := by
  exact ⟨D.normalizedCellRay_norm hP hG i,
    (D.normalizedCellRay_inner_parent hP hG i).trans
      (D.antiprism_height hP hG (polygonFace_unitPolygon hP hG).1 i hi)⟩

/-- An actual duoprism slot gives the two unit lateral rays, their common
parent projection, and the regular polygon Gram entry. -/
theorem duoprism_normalizedCellRay_metrics {n q : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (hn4 : n ≠ 4) (hq : 3 ≤ q) (i : Fin D.length)
    (hK : Congruent (D.facet i) (duoprismModel n q)) :
    (‖D.normalizedCellRay hP hG i‖ = 1 ∧
      ⟪D.normalizedCellRay hP hG i, polygonParentOffset hP hG⟫ = 1 / 2) ∧
    (‖D.normalizedCellRay hP hG (i.val + 1)‖ = 1 ∧
      ⟪D.normalizedCellRay hP hG (i.val + 1), polygonParentOffset hP hG⟫ = 1 / 2) ∧
    ⟪D.normalizedCellRay hP hG i, D.normalizedCellRay hP hG (i.val + 1)⟫ =
      Real.cos (Real.pi * (1 - 2 / (q : ℝ))) := by
  obtain ⟨ha, hb, hangle⟩ := D.duoprism_slot hP hG hn4 hq i hK
  refine ⟨D.prism_normalizedCellRay hP hG i ha,
    D.prism_normalizedCellRay hP hG (i.val + 1) hb, ?_⟩
  rw [D.normalizedCellRay_inner_next hP hG i, hangle]

/-- The two actual rays of an antiprism-prism slot are orthogonal. -/
theorem antiprismPrism_normalizedCellRay_inner {n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (hn4 : n ≠ 4) (i : Fin D.length)
    (hK : Congruent (D.facet i) (antiprismPrismModel n)) :
    ⟪D.normalizedCellRay hP hG i, D.normalizedCellRay hP hG (i.val + 1)⟫ = 0 := by
  rw [D.normalizedCellRay_inner_next hP hG i,
    (D.antiprismPrism_slot hP hG hn4 i hK).2, Real.cos_pi_div_two]

end ActualPolygonCycle
end Uniform5.Composition
