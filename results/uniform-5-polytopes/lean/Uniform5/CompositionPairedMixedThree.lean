import Uniform5.CompositionPairedTypeIIMetrics
import Uniform5.CompositionPairedTypeIVertices

/-! The actual mixed Type I / Type II case cannot have a three-slot
Type I fan: incidence forces a corner whose antiprism diagonal would
have to be the chord of a regular polygon. -/
noncomputable section
namespace Uniform5.Composition
open Set
namespace TypeIFanChart
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

include T in
theorem paired_k3_typeII_partner_impossible
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} {m : ℕ}
    (hH : PolygonFace P H m) (hm : 17 ≤ m) (hvH : v ∈ H.extremePoints ℝ)
    (hGH : G ≠ H) (A : ActualPolygonCycle P H) (U : TypeIIActualFanData A v m)
    (hcover : TwoLargeFacesCoverAt P v G H) (hlen : D.length = 3)
    (j : Fin D.length) (hHK : H ⊆ D.facet j)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i))) : False := by
  have hc := T.common_facet_partner_edges hP hG hn hvG hH hm hvH hGH q hq hmodel j hHK
  have hz := T.paired_k3_lateral_mem_partner classification3D classification4D N S
    hLIB hS1 hB2 hP hG hn hvG hH A hcover hlen j hc.1 hc.2.1
  obtain ⟨k, hk⟩ := (A.facet_coverage (D.facet j)).mp ⟨(D.facet_incidence j).1, hHK⟩
  have hGk : G ⊆ A.facet k := hk.symm ▸ (D.facet_incidence j).2.1
  have hop := U.partner_facet_eq_opposite hP hH hm hvH hG hn hvG hGH.symm k hGk
  have he : D.facet j = A.facet U.opposite := hk.symm.trans (congrArg A.facet hop)
  have hout : T.lateral (finRotate D.length (finRotate D.length j)) ∉
      (U.figureFacet hP U.opposite).extremePoints ℝ := by
    change _ ∉ (A.facet U.opposite ∩ _).extremePoints ℝ
    rw [← he]
    exact T.remaining_not_facet_vertices hP hG hvG j
  obtain ⟨u, hu, hdiag⟩ := U.fan_outside_opposite_diagonal hP hH hm hvH hz hout
  have hcd : T.lateral j ≠ T.lateral (finRotate D.length j) :=
    fun he => (finRotate_ne_and_twice_ne D.length_ge j).1 (T.lateral_injective he).symm
  have hpoly := finitePolytope_face (uniform_finitePolytope hP.1) hH.1 (polygonFace_nonempty hH)
  have hup := (finitePolytope_planar_neighbors hpoly hH.2.1 hc.1 hc.2.1 hcd u).mp hu
  have hdist1 := T.lateral_dist hP hG (by omega) (by omega) hvG (finRotate D.length j) (hq _) (hmodel _)
  have hdist2 := T.lateral_dist hP hG (by omega) (by omega) hvG
    (finRotate D.length (finRotate D.length j)) (hq _) (hmodel _)
  rw [finRotate_three_closed hlen] at hdist2
  rcases hup with rfl | rfl
  · exact CaseB.antiprism_diagonal_not_chord (by exact_mod_cast hm) (hq _)
      (hdiag.symm.trans hdist2)
  · exact CaseB.antiprism_diagonal_not_chord (by exact_mod_cast hm) (hq _)
      (hdiag.symm.trans ((dist_comm _ _).trans hdist1))

end TypeIFanChart
end Uniform5.Composition
