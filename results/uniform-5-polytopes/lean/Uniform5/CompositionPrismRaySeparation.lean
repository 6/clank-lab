import Uniform5.CompositionCaseBTypeIIRadius

/-! Distinct actual prism cells give distinct nonopposite normal rays. -/
noncomputable section
namespace Uniform5.Composition.ActualPolygonCycle
open Set
open scoped RealInnerProductSpace
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- Equal centers of two actual cells force the cells to coincide, since
both centers lie in the relative interiors of their faces. -/
theorem cellCenter_injective (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) :
    Function.Injective (fun i : Fin D.length => D.cellCenter hP hG i) := by
  intro i j he
  change D.cellCenter hP hG i = D.cellCenter hP hG j at he
  have hi : D.cellCenter hP hG i ∈ intrinsicInterior ℝ (D.cell i) :=
    vertexCentroid_mem_intrinsicInterior _
  have hj : D.cellCenter hP hG j ∈ intrinsicInterior ℝ (D.cell j) :=
    vertexCentroid_mem_intrinsicInterior _
  have hcells : D.cell i = D.cell j := Set.Subset.antisymm
    (face_subset_of_intrinsicInterior_mem (D.cell_face i) (D.cell_face j) hi
      (by rw [he]; exact intrinsicInterior_subset hj))
    (face_subset_of_intrinsicInterior_mem (D.cell_face j) (D.cell_face i) hj
      (by rw [← he]; exact intrinsicInterior_subset hi))
  exact Fin.ext (D.cell_injective i.isLt j.isLt hcells)

/-- Two distinct actual prism cells have scalar product strictly between
minus one and one. Their equal positive parent projection excludes antipodes. -/
theorem prism_ray_inner_bounds {n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (i j : Fin D.length) (hij : i ≠ j)
    (hi : Congruent (D.cell i) (polygonPrismModel n))
    (hj : Congruent (D.cell j) (polygonPrismModel n)) :
    -1 < ⟪D.normalizedCellRay hP hG i, D.normalizedCellRay hP hG j⟫ ∧
      ⟪D.normalizedCellRay hP hG i, D.normalizedCellRay hP hG j⟫ < 1 := by
  let x := D.normalizedCellRay hP hG i
  let y := D.normalizedCellRay hP hG j
  obtain ⟨hx, hxW⟩ := D.prism_normalizedCellRay hP hG i hi
  obtain ⟨hy, hyW⟩ := D.prism_normalizedCellRay hP hG j hj
  change ‖x‖ = 1 at hx
  change ‖y‖ = 1 at hy
  change ⟪x, polygonParentOffset hP hG⟫ = 1 / 2 at hxW
  change ⟪y, polygonParentOffset hP hG⟫ = 1 / 2 at hyW
  have hneq : x ≠ y := by
    intro he
    have hhi : ‖D.cellCenter hP hG i - polygonCenter hP hG‖ = 1 / 2 := by
      rw [← D.height_eq hP hG]; exact D.prism_height hP hG i hi
    have hhj : ‖D.cellCenter hP hG j - polygonCenter hP hG‖ = 1 / 2 := by
      rw [← D.height_eq hP hG]; exact D.prism_height hP hG j hj
    change ‖_‖⁻¹ • _ = ‖_‖⁻¹ • _ at he
    rw [hhi, hhj] at he
    have hc : D.cellCenter hP hG i = D.cellCenter hP hG j := by
      have hh := (smul_right_injective (Space 5) (inv_ne_zero (by norm_num : (1 / 2 : ℝ) ≠ 0))) he
      exact sub_left_injective hh
    exact hij (D.cellCenter_injective hP hG hc)
  have hnopp : x ≠ -y := by
    intro he
    have he' := congrArg (fun u => ⟪u, polygonParentOffset hP hG⟫) he
    change ⟪x, polygonParentOffset hP hG⟫ = ⟪-y, polygonParentOffset hP hG⟫ at he'
    rw [inner_neg_left, hxW, hyW] at he'
    norm_num at he'
  have hup : ⟪x, y⟫ < 1 := by
    have hh := (inner_lt_norm_mul_iff_real (x := x) (y := y)).mpr
      (by simpa only [hx, hy, one_smul] using hneq)
    simpa only [hx, hy, one_mul] using hh
  have hlo : ⟪x, -y⟫ < 1 := by
    have hh := (inner_lt_norm_mul_iff_real (x := x) (y := -y)).mpr
      (by simpa only [norm_neg, hx, hy, one_smul] using hnopp)
    simpa only [norm_neg, hx, hy, one_mul] using hh
  rw [inner_neg_right] at hlo
  exact ⟨by linarith, hup⟩

end Uniform5.Composition.ActualPolygonCycle
