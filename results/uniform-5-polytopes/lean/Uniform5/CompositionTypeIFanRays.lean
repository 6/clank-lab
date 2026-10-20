import Uniform5.CompositionTypeIFanMetrics

/-! The coherent lateral neighbor is the actual normalized prism-cell
center ray based at the root. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unit_cross_inner_zero {v a z : E} (ha : ‖a - v‖ = 1)
    (hz : ‖z - v‖ = 1) (haz : dist a z = Real.sqrt 2) : ⟪z - v, a - v⟫ = 0 := by
  have he : ‖(z - v) - (a - v)‖ ^ 2 = 2 := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm, dist_comm, haz,
      Real.sq_sqrt (by norm_num)]
  rw [norm_sub_sq_real, ha, hz] at he
  nlinarith

namespace TypeIFanChart
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

theorem lateral_eq_normalizedCellRay (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hvG : v ∈ G.extremePoints ℝ)
    (i : Fin D.length) {q : ℕ} (hq : 3 ≤ q)
    (hmodel : Congruent (D.facet i) (duoprismModel n q))
    (hcell : Congruent (D.cell i) (polygonPrismModel n)) :
    T.lateral i - v = D.normalizedCellRay hP hG i := by
  let z := T.lateral i
  let c := D.cellCenter hP hG i
  let f := ActualPolygonCycle.polygonCenter hP hG
  have hCU := D.cell_unitUniform hP hG i
  have hC := D.cell_face i
  have hez : Edge (D.cell i) v z := (T.cell_neighbors i z).mpr (Or.inr (Or.inr rfl))
  have haG := (T.polygon_neighbors T.a).mpr (Or.inl rfl)
  have hbG := (T.polygon_neighbors T.b).mpr (Or.inr rfl)
  have haP := (edge_face_iff (uniform_finitePolytope hP.1) hG.1 hvG.1 haG.2.1.1).mpr haG
  have hbP := (edge_face_iff (uniform_finitePolytope hP.1) hG.1 hvG.1 hbG.2.1.1).mpr hbG
  have hz : ‖z - v‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hCU.2 _ _ hez
  have ha : ‖T.a - v‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hP.2 _ _ haP
  have hb : ‖T.b - v‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hP.2 _ _ hbP
  obtain ⟨haz, hbz⟩ := T.cross_dist hP hG hn hn4 hvG i hq hmodel
  have hia := unit_cross_inner_zero ha hz haz
  have hib := unit_cross_inner_zero hb hz hbz
  have hdir : (affineSpan ℝ G).direction ≤ LinearMap.ker (innerSL ℝ (z - v)).toLinearMap := by
    rw [← planar_three_vertices_span hG.2.1 hvG haG.2.1 hbG.2.1
      haG.2.2.1 hbG.2.2.1 T.ab_ne]
    apply Submodule.span_le.mpr
    rintro w (rfl | rfl)
    · exact hia
    · exact hib
  have hfG : f ∈ G := intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior _)
  have hfv : f - v ∈ (affineSpan ℝ G).direction :=
    AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ G hfG) (subset_affineSpan ℝ G hvG.1)
  have hif : ⟪z - v, f - v⟫ = 0 := hdir hfv
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hCU.1
  have hsv : ‖v - c‖ ^ 2 = intrinsicRadius (D.cell i) ^ 2 := hs v hez.1
  have hsz : ‖z - c‖ ^ 2 = intrinsicRadius (D.cell i) ^ 2 := hs z hez.2.1
  have hic : ⟪z - v, c - v⟫ = 1 / 2 := by
    have he := norm_sub_sq_real (z - v) (c - v)
    rw [sub_sub_sub_cancel_right, hz, norm_sub_rev c v, hsv, hsz] at he
    nlinarith
  have hicf : ⟪z - v, c - f⟫ = 1 / 2 := by
    rw [show c - f = (c - v) - (f - v) by abel, inner_sub_right, hic, hif]
    ring
  have hcf : ‖c - f‖ = 1 / 2 := by
    change ‖D.cellCenter hP hG i - ActualPolygonCycle.polygonCenter hP hG‖ = _
    rw [← D.height_eq hP hG]
    exact D.prism_height hP hG i hcell
  have hi : ⟪z - v, D.normalizedCellRay hP hG i⟫ = 1 := by
    change ⟪z - v, ‖c - f‖⁻¹ • (c - f)⟫ = 1
    rw [real_inner_smul_right, hicf, hcf]
    norm_num
  have hr := (D.prism_normalizedCellRay hP hG i hcell).1
  have he := norm_sub_sq_real (z - v) (D.normalizedCellRay hP hG i)
  rw [hz, hr, hi] at he
  have hnzero : ‖(z - v) - D.normalizedCellRay hP hG i‖ = 0 := by
    nlinarith [norm_nonneg ((z - v) - D.normalizedCellRay hP hG i)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnzero)

end TypeIFanChart
end Uniform5.Composition
