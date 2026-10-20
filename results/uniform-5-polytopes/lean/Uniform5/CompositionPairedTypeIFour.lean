import Uniform5.CompositionPairedTypeIThree
import Uniform5.CompositionPairedCommonFacet
import Uniform5.CompositionPairedFourAngles

/-! Actual Type I / Type I paired fans cannot have a four-slot cycle.
The neighbor lists, partner membership, and unit distances are all derived. -/
noncomputable section
namespace Uniform5.Composition.TypeIFanChart
open Set
open scoped BigOperators
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

theorem paired_k4_lateral_escape
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} {m : ℕ}
    (hH : PolygonFace P H m) (A : ActualPolygonCycle P H)
    (hcover : TwoLargeFacesCoverAt P v G H) (hlen : D.length = 4) (j : Fin D.length)
    (hcH : Edge H v (T.lateral j))
    (hdH : Edge H v (T.lateral (finRotate D.length j))) :
    T.pairedSixLabels hlen j 4 ∈ actualPolygonFanVertices hP A v ∨
      T.pairedSixLabels hlen j 5 ∈ actualPolygonFanVertices hP A v := by
  let p := T.pairedSixLabels hlen j
  have hp (i : Fin 6) := fan_vertex_extreme hP hG hvG (T.pairedSixLabels_mem_fan hP hG hvG hlen j i)
  have hK := (D.facet_incidence j).1
  have hvK : v ∈ (D.facet j).extremePoints ℝ := by
    rw [face_extremePoints_eq hK.1]
    exact ⟨(D.facet_incidence j).2.1 hvG.1, hG.1.2.extremePoints_subset_extremePoints hvG⟩
  have hplace := unitUniform5_facet_figure_placement hP hK hvK
  apply finitePolytope_paired_k4_escape hplace.1 hplace.2.1 p hp (actualPolygonFanVertices hP A v)
  · intro F hF hc hd x hx
    obtain ⟨i, hi⟩ := unitUniform5_figure_facet_in_polygon_fan hP hH A hcH hdH
      (fun he => (finRotate_ne_and_twice_ne D.length_ge j).1 (T.lateral_injective he).symm)
      hF hc hd
    exact ⟨i, hi ▸ hx⟩
  · intro hz w
    exact T.paired_k4_outside_neighbors_4 classification3D classification4D N S
      hLIB hS1 hB2 hP hG hn hvG A hcover hlen j hz w
  · intro hz w
    exact T.paired_k4_outside_neighbors_5 classification3D classification4D N S
      hLIB hS1 hB2 hP hG hn hvG A hcover hlen j hz w

include T in
theorem paired_k4_typeI_partner_impossible
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} {m : ℕ}
    (hH : PolygonFace P H m) (hm : 17 ≤ m) (hvH : v ∈ H.extremePoints ℝ)
    (hGH : G ≠ H) (A : ActualPolygonCycle P H) (U : TypeIFanChart A v m)
    (hcover : TwoLargeFacesCoverAt P v G H) (hlen : D.length = 4) (j : Fin D.length)
    (hHK : H ⊆ D.facet j)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hangle : (∑ i, (1 - 2 / (q i : ℝ))) < 2)
    (r : Fin A.length → ℕ) (hr : ∀ i, 3 ≤ r i)
    (hpartner : ∀ i, Congruent (A.facet i) (duoprismModel m (r i))) : False := by
  obtain ⟨hcH, hdH, hqm⟩ := T.common_facet_partner_edges hP hG hn hvG hH hm hvH hGH q hq hmodel j hHK
  have hsmall := paired_four_small_parameters hlen q hq j (hqm.symm ▸ hm) hangle
  let p := T.pairedSixLabels hlen j
  have hcd : T.lateral j ≠ T.lateral (finRotate D.length j) :=
    fun he => (finRotate_ne_and_twice_ne D.length_ge j).1 (T.lateral_injective he).symm
  have hmet (s : Fin 6) (hs : p s ∈ actualPolygonFanVertices hP A v)
      (hs2 : s ≠ 2) (hs3 : s ≠ 3) :
      dist (p s) (p 2) = Real.sqrt 2 ∧ dist (p s) (p 3) = Real.sqrt 2 :=
    U.fan_metric_at_endpoints hP hH (by omega) (by omega) hvH r hr hpartner hcH hdH hcd hs
      (fun he => hs2 (p.injective he)) (fun he => hs3 (p.injective he))
  have hq₂ := hsmall (finRotate D.length j) (finRotate_ne_and_twice_ne D.length_ge j).1
  have hq₄ : q (finRotate D.length (finRotate D.length (finRotate D.length j))) = 3 := by
    apply hsmall
    intro he
    have hh := congrArg (finRotate D.length) he
    rw [finRotate_four_closed hlen] at hh
    exact (finRotate_ne_and_twice_ne D.length_ge j).1 hh.symm
  have hunit4 : dist (p 4) (p 3) = 1 := by
    have h := T.lateral_dist hP hG (by omega) (by omega) hvG
      (finRotate D.length j) (hq _) (hmodel _)
    rw [hq₂, Nat.cast_ofNat, CaseB.case_chord_three] at h
    exact (dist_comm _ _).trans h
  have hunit5 : dist (p 5) (p 2) = 1 := by
    have h := T.lateral_dist hP hG (by omega) (by omega) hvG
      (finRotate D.length (finRotate D.length (finRotate D.length j))) (hq _) (hmodel _)
    rw [finRotate_four_closed hlen, hq₄, Nat.cast_ofNat, CaseB.case_chord_three] at h
    exact h
  have hno4 : p 4 ∉ actualPolygonFanVertices hP A v := by
    intro hs
    have hh := (hmet 4 hs (by decide) (by decide)).2
    rw [hunit4] at hh
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hno5 : p 5 ∉ actualPolygonFanVertices hP A v := by
    intro hs
    have hh := (hmet 5 hs (by decide) (by decide)).1
    rw [hunit5] at hh
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact (T.paired_k4_lateral_escape classification3D classification4D N S hLIB hS1 hB2
    hP hG hn hvG hH A hcover hlen j hcH hdH).elim hno4 hno5

end Uniform5.Composition.TypeIFanChart
