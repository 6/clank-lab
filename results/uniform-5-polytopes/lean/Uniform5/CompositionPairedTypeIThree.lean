import Uniform5.CompositionTypeIPairedNeighbors
import Uniform5.CompositionPairedIncidence
import Uniform5.CompositionPolygonFanMembership
import Uniform5.CompositionPlanarNeighbors
import Uniform5.CaseBCaseMetrics

/-! The actual three-slot Type I fan forces its remaining lateral
vertex into the partner fan, and actual Type I partner metrics force
both remaining parameters to be four. -/
noncomputable section
namespace Uniform5.Composition
open Set

namespace TypeIFanChart
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

include T in
theorem fan_metric_at_endpoints (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hvG : v ∈ G.extremePoints ℝ)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    {c d z : Space 5} (hc : Edge G v c) (hd : Edge G v d) (hcd : c ≠ d)
    (hz : z ∈ actualPolygonFanVertices hP D v) (hzc : z ≠ c) (hzd : z ≠ d) :
    dist z c = Real.sqrt 2 ∧ dist z d = Real.sqrt 2 := by
  have hpoly := finitePolytope_face (uniform_finitePolytope hP.1) hG.1 (polygonFace_nonempty hG)
  have hp := finitePolytope_planar_neighbors hpoly hG.2.1 hc hd hcd
  have hza : z ≠ T.a := by
    intro he
    rcases (hp T.a).mp ((T.polygon_neighbors T.a).mpr (Or.inl rfl)) with h | h
    · exact hzc (he.trans h)
    · exact hzd (he.trans h)
  have hzb : z ≠ T.b := by
    intro he
    rcases (hp T.b).mp ((T.polygon_neighbors T.b).mpr (Or.inr rfl)) with h | h
    · exact hzc (he.trans h)
    · exact hzd (he.trans h)
  have hm := T.fan_metric hP hG hn hn4 hvG q hq hmodel hz hza hzb
  constructor
  · rcases (T.polygon_neighbors c).mp hc with rfl | rfl
    · exact hm.1
    · exact hm.2
  · rcases (T.polygon_neighbors d).mp hd with rfl | rfl
    · exact hm.1
    · exact hm.2

theorem paired_k3_lateral_mem_partner
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} {m : ℕ}
    (hH : PolygonFace P H m) (A : ActualPolygonCycle P H)
    (hcover : TwoLargeFacesCoverAt P v G H) (hlen : D.length = 3) (j : Fin D.length)
    (hcH : Edge H v (T.lateral j))
    (hdH : Edge H v (T.lateral (finRotate D.length j))) :
    T.pairedFiveLabels j 4 ∈ actualPolygonFanVertices hP A v := by
  let p := T.pairedFiveLabels j
  have hp (i : Fin 5) := fan_vertex_extreme hP hG hvG (T.pairedFiveLabels_mem_fan hP hG hvG j i)
  have hK := (D.facet_incidence j).1
  have hvK : v ∈ (D.facet j).extremePoints ℝ := by
    rw [face_extremePoints_eq hK.1]
    exact ⟨(D.facet_incidence j).2.1 hvG.1, hG.1.2.extremePoints_subset_extremePoints hvG⟩
  have hplace := unitUniform5_facet_figure_placement hP hK hvK
  apply finitePolytope_paired_k3_vertex_in_partner hplace.1 hplace.2.1 p hp
    (actualPolygonFanVertices hP A v)
  · intro F hF hc hd x hx
    obtain ⟨i, hi⟩ := unitUniform5_figure_facet_in_polygon_fan hP hH A hcH hdH
      (fun he => (finRotate_ne_and_twice_ne D.length_ge j).1 (T.lateral_injective he).symm)
      hF hc hd
    exact ⟨i, hi ▸ hx⟩
  · intro hz w
    exact T.paired_k3_outside_neighbors classification3D classification4D N S
      hLIB hS1 hB2 hP hG hn hvG A hcover hlen j hz w

theorem paired_k3_typeI_partner_parameters
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} {m : ℕ}
    (hH : PolygonFace P H m) (hm : 17 ≤ m) (hvH : v ∈ H.extremePoints ℝ)
    (A : ActualPolygonCycle P H) (U : TypeIFanChart A v m)
    (hcover : TwoLargeFacesCoverAt P v G H) (hlen : D.length = 3) (j : Fin D.length)
    (hcH : Edge H v (T.lateral j))
    (hdH : Edge H v (T.lateral (finRotate D.length j)))
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (r : Fin A.length → ℕ) (hr : ∀ i, 3 ≤ r i)
    (hpartner : ∀ i, Congruent (A.facet i) (duoprismModel m (r i))) :
    q (finRotate D.length j) = 4 ∧ q (finRotate D.length (finRotate D.length j)) = 4 := by
  have hz := T.paired_k3_lateral_mem_partner classification3D classification4D N S
    hLIB hS1 hB2 hP hG hn hvG hH A hcover hlen j hcH hdH
  let p := T.pairedFiveLabels j
  have hcd : T.lateral j ≠ T.lateral (finRotate D.length j) :=
    fun he => (finRotate_ne_and_twice_ne D.length_ge j).1 (T.lateral_injective he).symm
  have hzc : p 4 ≠ p 2 := fun he => by have := p.injective he; simp only [Fin.reduceEq] at this
  have hzd : p 4 ≠ p 3 := fun he => by have := p.injective he; simp only [Fin.reduceEq] at this
  have hmet := U.fan_metric_at_endpoints hP hH (by omega) (by omega) hvH r hr hpartner
    hcH hdH hcd hz hzc hzd
  have hq₂ := T.lateral_dist hP hG (by omega) (by omega) hvG
    (finRotate D.length j) (hq _) (hmodel _)
  have hq₃ := T.lateral_dist hP hG (by omega) (by omega) hvG
    (finRotate D.length (finRotate D.length j)) (hq _) (hmodel _)
  rw [finRotate_three_closed hlen] at hq₃
  constructor
  · apply (CaseB.case_chord_nat_eq_sqrt_two_iff (hq _)).mp
    exact hq₂.symm.trans ((dist_comm _ _).trans hmet.2)
  · apply (CaseB.case_chord_nat_eq_sqrt_two_iff (hq _)).mp
    exact hq₃.symm.trans hmet.1

end TypeIFanChart
end Uniform5.Composition
