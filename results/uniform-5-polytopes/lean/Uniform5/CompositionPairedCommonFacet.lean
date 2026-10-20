import Uniform5.CompositionTypeIFanMetrics
import Uniform5.CompositionPolygonFanMembership
import Uniform5.CaseBCaseMetrics

/-! Two distinct actual large polygons in a common Type I fan facet
use the complementary two actual lateral neighbors of that facet. -/
noncomputable section
namespace Uniform5.Composition.TypeIFanChart
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

theorem common_facet_partner_edges (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ)
    {H : Set (Space 5)} {m : ℕ} (hH : PolygonFace P H m) (hm : 17 ≤ m)
    (hvH : v ∈ H.extremePoints ℝ) (hGH : G ≠ H)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (j : Fin D.length) (hHK : H ⊆ D.facet j) :
    Edge H v (T.lateral j) ∧ Edge H v (T.lateral (finRotate D.length j)) ∧ q j = m := by
  have hv := hG.1.2.extremePoints_subset_extremePoints hvG
  obtain ⟨c, d, he, hcH, hdH, _⟩ := unitUniform5_polygon_vertexFigure_edge hP hv hH hvH.1
  have hcd := he.2.2.1
  have hK := (D.facet_incidence j).1
  have hHf : IsConvexFace (D.facet j) H := face_restrict hH.1 hK.1.2.1 hHK
  have hKfin := uniform_finitePolytope (D.facet_unitUniform hP j).1
  have hcK := (edge_face_iff hKfin hHf hvH.1 hcH.2.1.1).mpr hcH
  have hdK := (edge_face_iff hKfin hHf hvH.1 hdH.2.1.1).mpr hdH
  have hdist : dist c d = CaseB.chord m := polygonFace_neighbor_chord hP hH hcH hdH hcd
  have hch : CaseB.chord m ≠ Real.sqrt 2 := by
    intro hh
    have heq := (CaseB.case_chord_nat_eq_sqrt_two_iff (by omega : 3 ≤ m)).mp hh
    omega
  have hcross0 := T.cross_dist hP hG (by omega) (by omega) hvG j (hq j) (hmodel j)
  have hcross1 := T.cross_dist hP hG (by omega) (by omega) hvG
    (finRotate D.length j) (hq _) (hmodel _)
  have haG := (T.polygon_neighbors T.a).mpr (Or.inl rfl)
  have hbG := (T.polygon_neighbors T.b).mpr (Or.inr rfl)
  have hc : c ≠ T.a ∧ c ≠ T.b := by
    constructor
    · intro hca
      subst c
      rcases (T.facet_neighbors j d).mp hdK with hda | hdb | hd0 | hd1
      · exact hcd hda.symm
      · subst d
        exact hGH (polygonFace_eq_of_common_neighbor_pair hG hH haG hbG hcH hdH T.ab_ne)
      · exact hch (hdist.symm.trans (hd0 ▸ hcross0.1))
      · exact hch (hdist.symm.trans (hd1 ▸ hcross1.1))
    · intro hcb
      subst c
      rcases (T.facet_neighbors j d).mp hdK with hda | hdb | hd0 | hd1
      · subst d
        exact hGH (polygonFace_eq_of_common_neighbor_pair hG hH haG hbG hdH hcH T.ab_ne)
      · exact hcd hdb.symm
      · exact hch (hdist.symm.trans (hd0 ▸ hcross0.2))
      · exact hch (hdist.symm.trans (hd1 ▸ hcross1.2))
  have hd : d ≠ T.a ∧ d ≠ T.b := by
    constructor
    · intro hda
      subst d
      rcases (T.facet_neighbors j c).mp hcK with hca | hcb | hc0 | hc1
      · exact hc.1 hca
      · exact hc.2 hcb
      · apply hch
        rw [← hdist, hc0, dist_comm]
        exact hcross0.1
      · apply hch
        rw [← hdist, hc1, dist_comm]
        exact hcross1.1
    · intro hdb
      subst d
      rcases (T.facet_neighbors j c).mp hcK with hca | hcb | hc0 | hc1
      · exact hc.1 hca
      · exact hc.2 hcb
      · apply hch
        rw [← hdist, hc0, dist_comm]
        exact hcross0.2
      · apply hch
        rw [← hdist, hc1, dist_comm]
        exact hcross1.2
  have hcp : c = T.lateral j ∨ c = T.lateral (finRotate D.length j) := by
    rcases (T.facet_neighbors j c).mp hcK with hh | hh | hh | hh
    · exact (hc.1 hh).elim
    · exact (hc.2 hh).elim
    · exact Or.inl hh
    · exact Or.inr hh
  have hdp : d = T.lateral j ∨ d = T.lateral (finRotate D.length j) := by
    rcases (T.facet_neighbors j d).mp hdK with hh | hh | hh | hh
    · exact (hd.1 hh).elim
    · exact (hd.2 hh).elim
    · exact Or.inl hh
    · exact Or.inr hh
  have hedge : Edge H v (T.lateral j) ∧ Edge H v (T.lateral (finRotate D.length j)) := by
    rcases hcp with rfl | rfl <;> rcases hdp with rfl | rfl
    · exact (hcd rfl).elim
    · exact ⟨hcH, hdH⟩
    · exact ⟨hdH, hcH⟩
    · exact (hcd rfl).elim
  refine ⟨hedge.1, hedge.2, ?_⟩
  have hne : T.lateral j ≠ T.lateral (finRotate D.length j) :=
    fun he => (finRotate_ne_and_twice_ne D.length_ge j).1 (T.lateral_injective he).symm
  have hmch := polygonFace_neighbor_chord hP hH hedge.1 hedge.2 hne
  have hqch := T.lateral_dist hP hG (by omega) (by omega) hvG j (hq j) (hmodel j)
  have heq := CaseB.chord_strictMono.injOn (by change (3 : ℝ) ≤ q j; exact_mod_cast hq j)
    (by change (3 : ℝ) ≤ m; exact_mod_cast (show 3 ≤ m by omega)) (hqch.symm.trans hmch)
  exact_mod_cast heq

end Uniform5.Composition.TypeIFanChart
