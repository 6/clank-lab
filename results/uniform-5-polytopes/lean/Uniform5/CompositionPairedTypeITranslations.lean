import Uniform5.CompositionPairedTypeIVertices
import Uniform5.CompositionTypeIFanRays
import Uniform5.CompositionDuoprismSliceFaces

/-! Orthogonality and exact whole-polygon translations at the remaining
neighbor in the surviving paired Type I case. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

theorem facet_normal_of_figure_vertices {P K : Set (Space 5)}
    (hP : UnitUniform 5 P) (hK : Facet P K) {v d : Space 5}
    (hv : v ∈ P.extremePoints ℝ) (hvK : v ∈ K)
    (hperp : ∀ x ∈ (K ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ,
      ⟪d, x - v⟫ = 0) : d ∈ CaseB.normals K := by
  let B := AffineSubspace.mk' v (LinearMap.ker (innerSL ℝ d).toLinearMap)
  have hvK' : v ∈ K.extremePoints ℝ := by
    rw [face_extremePoints_eq hK.1]
    exact ⟨hvK, hv⟩
  have hp := unitUniform5_facet_figure_placement hP hK hvK'
  have hfin := finitePolytope_face hp.1 hp.2.2.1.1 hp.2.2.1.2.1
  have hspan : affineSpan ℝ K ≤ B := by
    rw [← actual_facet_root_figure_span hP hK hv hvK]
    apply affineSpan_le.mpr
    rintro x (rfl | hx)
    · exact AffineSubspace.self_mem_mk' _ _
    · rw [finitePolytope_eq_convexHull_extremePoints hfin] at hx
      exact convexHull_min (fun y hy => hperp y hy) B.convex hx
  intro x hx y hy
  have he := AffineSubspace.vsub_mem_direction
    (hspan (subset_affineSpan ℝ K hx)) (hspan (subset_affineSpan ℝ K hy))
  rw [AffineSubspace.direction_mk'] at he
  exact (real_inner_comm _ _).trans he

theorem normal_translate_point_offset {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {C : Set E} {v z d : E}
    (hv : v ∈ C) (hd : d ∈ CaseB.normals C) (hz : z - v ∈ CaseB.normals C)
    (hzd : z ∈ CaseB.translate C d) : d = z - v := by
  obtain ⟨x, hx, he⟩ := hzd
  change x + d = z at he
  have hh := CaseB.sum_injOn (C := C) (X := (CaseB.normals C : Set E)) (fun _ h => h)
    (show (x, d) ∈ C ×ˢ (CaseB.normals C : Set E) from ⟨hx, hd⟩)
    (show (v, z - v) ∈ C ×ˢ (CaseB.normals C : Set E) from ⟨hv, hz⟩)
    (show x + d = v + (z - v) by rw [he]; abel)
  exact congrArg Prod.snd hh

namespace TypeIFanChart
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

theorem paired_remaining_normal (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hvG : v ∈ G.extremePoints ℝ)
    (hlen : D.length = 3) (j : Fin D.length)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hq1 : q (finRotate D.length j) = 4)
    (hq2 : q (finRotate D.length (finRotate D.length j)) = 4) :
    T.lateral (finRotate D.length (finRotate D.length j)) - v ∈
      CaseB.normals (D.facet j) := by
  let z := T.lateral (finRotate D.length (finRotate D.length j))
  have hK := (D.facet_incidence j).1
  have hv := hG.1.2.extremePoints_subset_extremePoints hvG
  have hvK := (D.facet_incidence j).2.1 hvG.1
  have hunit (i : Fin D.length) : ‖T.lateral i - v‖ = 1 := by
    have he := (T.cell_neighbors i (T.lateral i)).mpr (Or.inr (Or.inr rfl))
    rw [← dist_eq_norm, dist_comm]
    exact (D.cell_unitUniform hP hG i).2 _ _ he
  have hroot (x : Space 5) (hx : Edge G v x) : ‖x - v‖ = 1 := by
    rw [← dist_eq_norm, dist_comm]
    exact hP.2 _ _ ((edge_face_iff (uniform_finitePolytope hP.1) hG.1 hvG.1 hx.2.1.1).mpr hx)
  have hcross := T.cross_dist hP hG hn hn4 hvG
    (finRotate D.length (finRotate D.length j)) (hq _) (hmodel _)
  have hdist1 := T.lateral_dist hP hG hn hn4 hvG (finRotate D.length j) (hq _) (hmodel _)
  have hdist2 := T.lateral_dist hP hG hn hn4 hvG
    (finRotate D.length (finRotate D.length j)) (hq _) (hmodel _)
  rw [hq1, (CaseB.case_chord_nat_eq_sqrt_two_iff (by norm_num : 3 ≤ 4)).mpr rfl] at hdist1
  rw [hq2, (CaseB.case_chord_nat_eq_sqrt_two_iff (by norm_num : 3 ≤ 4)).mpr rfl,
    finRotate_three_closed hlen] at hdist2
  apply facet_normal_of_figure_vertices hP hK hv hvK
  rw [T.facet_figure_vertices hP hG hvG j]
  rintro x (rfl | rfl | rfl | rfl)
  · exact unit_cross_inner_zero (hroot _ ((T.polygon_neighbors _).mpr (Or.inl rfl)))
      (hunit _) hcross.1
  · exact unit_cross_inner_zero (hroot _ ((T.polygon_neighbors _).mpr (Or.inr rfl)))
      (hunit _) hcross.2
  · exact unit_cross_inner_zero (hunit _) (hunit _) ((dist_comm _ _).trans hdist2)
  · exact unit_cross_inner_zero (hunit _) (hunit _) hdist1

theorem paired_remaining_polygon_translate (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hvG : v ∈ G.extremePoints ℝ)
    (hlen : D.length = 3) (j : Fin D.length)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hq1 : q (finRotate D.length j) = 4)
    (hq2 : q (finRotate D.length (finRotate D.length j)) = 4) :
    PolygonFace P (CaseB.translate G
      (T.lateral (finRotate D.length (finRotate D.length j)) - v)) n := by
  let i := finRotate D.length j
  let z := T.lateral (finRotate D.length (finRotate D.length j))
  have hK := (D.facet_incidence i).1
  have hzK := ((T.facet_neighbors i z).mpr (Or.inr (Or.inr (Or.inr rfl)))).2.1
  have hGK : PolygonFace (D.facet i) G n :=
    ⟨face_restrict hG.1 hK.1.2.1 (D.facet_incidence i).2.1, hG.2⟩
  obtain ⟨d, hd, hF, hzF⟩ := unitUniform4_duoprism_polygon_translate
    (D.facet_unitUniform hP i) hn (hq i) (hmodel i) hGK hn4 hzK
  have hnK := T.paired_remaining_normal hP hG hn hn4 hvG hlen j q hq hmodel hq1 hq2
  have hnG : z - v ∈ CaseB.normals G := fun x hx y hy =>
    hnK x ((D.facet_incidence j).2.1 hx) y ((D.facet_incidence j).2.1 hy)
  have he := normal_translate_point_offset hvG.1 hd hnG hzF
  rw [he] at hF
  exact polygonFace_trans hK.1 hF

end TypeIFanChart
end Uniform5.Composition
