import Uniform5.CompositionTypeIIPartnerEndpoints
import Uniform5.CompositionTypeIIPairedNeighbors
import Uniform5.CompositionPairedIncidence

/-! The actual paired Type II / Type II configuration is impossible.
The simple-vertex forcing step and metric contradiction use only actual
fan incidence and the coherent charts constructed from the two cycles. -/
noncomputable section
namespace Uniform5.Composition
open Set

namespace TypeIIActualFanData
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIIActualFanData D v n)

theorem base_x_mem_partner
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} {m : ℕ}
    (hH : PolygonFace P H m) (A : ActualPolygonCycle P H)
    (hcover : TwoLargeFacesCoverAt P v G H)
    (hcH : Edge H v (T.lateral (finRotate D.length T.anti)))
    (hdH : Edge H v (T.lateral ((finRotate D.length).symm T.anti))) :
    T.base.x ∈ actualPolygonFanVertices hP A v := by
  let e : Fin 5 ↪ Fin 6 := ⟨![0, 3, 4, 5, 2], by decide⟩
  let p : Fin 5 ↪ Space 5 :=
    ⟨fun i => T.points (e i), (T.points_injective hG (by omega)).comp e.injective⟩
  have hp (i : Fin 5) : p i ∈ (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ := by
    apply TypeIFanChart.fan_vertex_extreme hP hG hvG
    rw [T.mem_fan_vertices hP hG hn hvG]
    fin_cases i <;> simp [p, e, points]
  have hcd : T.lateral (finRotate D.length T.anti) ≠
      T.lateral ((finRotate D.length).symm T.anti) := fun hh => by
    have hh' := T.points_injective hG (by omega) (show T.points 4 = T.points 5 from hh)
    exact (by decide : (4 : Fin 6) ≠ 5) hh'
  have hvK : v ∈ (D.facet T.anti).extremePoints ℝ := by
    rw [face_extremePoints_eq (D.facet_incidence T.anti).1.1]
    exact ⟨(D.facet_incidence T.anti).2.1 hvG.1,
      hG.1.2.extremePoints_subset_extremePoints hvG⟩
  have hpK := unitUniform5_facet_figure_placement hP (D.facet_incidence T.anti).1 hvK
  apply finitePolytope_paired_k3_vertex_in_partner hpK.1 hpK.2.1 p hp
    (actualPolygonFanVertices hP A v)
  · intro F hF hc hd x hx
    obtain ⟨i, hi⟩ := unitUniform5_figure_facet_in_polygon_fan hP hH A hcH hdH
      hcd hF hc hd
    exact ⟨i, hi ▸ hx⟩
  · intro hx w
    exact T.outside_partner_x_neighbors classification3D classification4D N S
      hLIB hS1 hB2 hP hG hn hvG A hcover hx w

include T in
theorem paired_typeII_impossible
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} {m : ℕ}
    (hH : PolygonFace P H m) (hm : 17 ≤ m) (hvH : v ∈ H.extremePoints ℝ)
    (hGH : G ≠ H) (A : ActualPolygonCycle P H) (U : TypeIIActualFanData A v m)
    (hcover : TwoLargeFacesCoverAt P v G H)
    (j : Fin D.length) (hHK : H ⊆ D.facet j) : False := by
  obtain ⟨hcH, hdH⟩ := T.common_facet_partner_edges hP hG hn hvG hH hm hvH hGH j hHK
  have hx := T.base_x_mem_partner classification3D classification4D N S
    hLIB hS1 hB2 hP hG hn hvG hH A hcover hcH hdH
  obtain ⟨k, hk⟩ := (A.facet_coverage (D.facet j)).mp ⟨(D.facet_incidence j).1, hHK⟩
  have hGK : G ⊆ A.facet k := by rw [hk]; exact (D.facet_incidence j).2.1
  obtain ⟨haG, hbG⟩ := U.common_facet_partner_edges hP hH hm hvH hG hn hvG hGH.symm k hGK
  have hxp (i : Fin 6) (hi : i ≠ 2) : T.base.x ≠ T.points i := fun he =>
    hi (T.points_injective hG (by omega) (show T.points 2 = T.points i from he)).symm
  have hxa : T.base.x ≠ T.base.a := hxp 0 (by decide)
  have hxb : T.base.x ≠ T.base.b := hxp 1 (by decide)
  have hxc : T.base.x ≠ T.lateral (finRotate D.length T.anti) := hxp 4 (by decide)
  have hxd : T.base.x ≠ T.lateral ((finRotate D.length).symm T.anti) := hxp 5 (by decide)
  have hcd : T.lateral (finRotate D.length T.anti) ≠
      T.lateral ((finRotate D.length).symm T.anti) := fun he => by
    have hh := T.points_injective hG (by omega) (show T.points 4 = T.points 5 from he)
    exact (by decide : (4 : Fin 6) ≠ 5) hh
  have hHp := finitePolytope_planar_neighbors
    (finitePolytope_face (uniform_finitePolytope hP.1) hH.1 (polygonFace_nonempty hH))
    hH.2.1 hcH hdH hcd
  have hnotH (z : Space 5) (hz : Edge H v z) : T.base.x ≠ z := by
    rcases (hHp z).mp hz with rfl | rfl
    · exact hxc
    · exact hxd
  have hnotG (z : Space 5) (hz : Edge G v z) : T.base.x ≠ z := by
    rcases (T.base.polygon_neighbors z).mp hz with rfl | rfl
    · exact hxa
    · exact hxb
  have hdist : dist T.base.x (T.lateral (finRotate D.length T.anti)) = Real.sqrt 2 := by
    have hh := T.first.apex_x
    rwa [T.first_base, T.first_apex] at hh
  have hrad := CaseB.case_antiprism_diagonal_sq_nonneg (n := (m : ℝ)) (by exact_mod_cast hm)
  have hdiag := CaseB.antiprism_diagonal_ne_sqrt_two (n := (m : ℝ)) (by exact_mod_cast hm)
  have hUx := CaseB.case_dist_eq_sqrt_of_sq_eq hrad U.base.diagonal_bx
  have hUy := CaseB.case_dist_eq_sqrt_of_sq_eq hrad U.base.diagonal_ay
  rcases (U.mem_fan_vertices hP hH hm hvH T.base.x).mp hx with ha | hb | hx | hy | ha | hb
  · exact hnotH _ ((U.base.polygon_neighbors _).mpr (Or.inl rfl)) ha
  · exact hnotH _ ((U.base.polygon_neighbors _).mpr (Or.inr rfl)) hb
  · rw [hx] at hdist
    rcases (U.base.polygon_neighbors _).mp hcH with hc | hc
    · rw [hc, dist_comm, U.base.side_ax] at hdist
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    · rw [hc, dist_comm, hUx] at hdist
      exact hdiag hdist
  · rw [hy] at hdist
    rcases (U.base.polygon_neighbors _).mp hcH with hc | hc
    · rw [hc, dist_comm, hUy] at hdist
      exact hdiag hdist
    · rw [hc, dist_comm, U.base.side_by] at hdist
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · exact hnotG _ haG ha
  · exact hnotG _ hbG hb

end TypeIIActualFanData

theorem unitUniform5_paired_typeII_impossible
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G H K : Set (Space 5)} (hP : UnitUniform 5 P) {n m : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n) (hH : PolygonFace P H m) (hm : 17 ≤ m)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ) (hvH : v ∈ H.extremePoints ℝ)
    (hGH : G ≠ H) (hcover : TwoLargeFacesCoverAt P v G H)
    (hK : Facet P K) (hGK : G ⊆ K) (hHK : H ⊆ K)
    (D : ActualPolygonCycle P G) (A : ActualPolygonCycle P H)
    (hD : D.CaseBTypeII n) (hA : A.CaseBTypeII m) : False := by
  obtain ⟨T⟩ := D.typeII_actual_fan hP hG hn hvG hD
  obtain ⟨U⟩ := A.typeII_actual_fan hP hH hm hvH hA
  obtain ⟨j, hj⟩ := (D.facet_coverage K).mp ⟨hK, hGK⟩
  exact T.paired_typeII_impossible classification3D classification4D N S hLIB hS1 hB2
    hP hG hn hvG hH hm hvH hGH A U hcover j (by rw [hj]; exact hHK)

end Uniform5.Composition
