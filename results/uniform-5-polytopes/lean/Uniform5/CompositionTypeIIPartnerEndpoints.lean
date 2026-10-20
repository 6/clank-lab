import Uniform5.CompositionTypeIICoherentEdges
import Uniform5.CompositionPyramidLongEdge
import Uniform5.CompositionPolygonFanMembership

/-! A second actual large polygon meets a Type II fan in its opposite
 tetrahedron, and uses exactly the two coherent pyramid apices. -/
noncomputable section
namespace Uniform5.Composition.TypeIIActualFanData
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIIActualFanData D v n)

theorem partner_facet_eq_opposite (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ)
    {H : Set (Space 5)} {m : ℕ} (hH : PolygonFace P H m) (hm : 17 ≤ m)
    (hvH : v ∈ H.extremePoints ℝ) (hGH : G ≠ H)
    (j : Fin D.length) (hHK : H ⊆ D.facet j) : j = T.opposite := by
  have hv := hG.1.2.extremePoints_subset_extremePoints hvG
  obtain ⟨c, d, he, hcH, hdH, _⟩ := unitUniform5_polygon_vertexFigure_edge hP hv hH hvH.1
  have hcd := he.2.2.1
  have hd : dist c d = CaseB.chord m := polygonFace_neighbor_chord hP hH hcH hdH hcd
  have hlong : Real.sqrt 2 < dist c d := by
    rw [hd, ← CaseB.chord_four]
    apply CaseB.chord_strictMono (by norm_num) (by change (3 : ℝ) ≤ m; exact_mod_cast (show 3 ≤ m by omega))
    exact_mod_cast (show 4 < m by omega)
  have hK := (D.facet_incidence j).1
  have hvK : v ∈ (D.facet j).extremePoints ℝ := by
    rw [face_extremePoints_eq hK.1]
    exact ⟨(D.facet_incidence j).2.1 hvG.1, hv⟩
  have hp := unitUniform5_facet_figure_placement hP hK hvK
  have heF : Edge (T.figureFacet hP j) c d :=
    (edge_face_iff hp.1 hp.2.2.1.1 ⟨hHK hcH.2.1.1, he.1.1⟩
      ⟨hHK hdH.2.1.1, he.2.1.1⟩).mp he
  rw [T.figureFacet_intrinsic hP hvG j] at heF
  have no_pyramid (B : AntiprismPrismNeighborChart (D.facet j) (D.cell T.anti) G v n)
      (hb : B.base = T.base) (hC : Facet (D.facet j) (D.cell T.anti)) : False := by
    have hh := B.long_edge_endpoints (D.facet_unitUniform hP j) hC (by omega) heF hlong
    rw [hb] at hh
    have haG := (T.base.polygon_neighbors T.base.a).mpr (Or.inl rfl)
    have hbG := (T.base.polygon_neighbors T.base.b).mpr (Or.inr rfl)
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hGH (polygonFace_eq_of_common_neighbor_pair hG hH haG hbG hcH hdH hcd)
    · exact hGH (polygonFace_eq_of_common_neighbor_pair hG hH haG hbG hdH hcH hcd.symm)
  rcases (finRotate_three_orbit T.length_three T.anti).2.2 j with rfl | rfl | hj
  · exact (no_pyramid T.first T.first_base (D.cell_facet hP hG _)).elim
  · have hk : (finRotate D.length).symm T.anti ∉ D.slotsAwayFrom T.anti := by
      rw [D.slotsAwayFrom_mem]
      exact fun hh => hh.2 ((finRotate D.length).apply_symm_apply T.anti)
    exact (no_pyramid T.last T.last_base (D.cell_facet_of_not_away hP hG _ _ hk)).elim
  · exact hj.trans T.opposite_eq.symm

theorem common_facet_partner_edges (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ)
    {H : Set (Space 5)} {m : ℕ} (hH : PolygonFace P H m) (hm : 17 ≤ m)
    (hvH : v ∈ H.extremePoints ℝ) (hGH : G ≠ H)
    (j : Fin D.length) (hHK : H ⊆ D.facet j) :
    Edge H v (T.lateral (finRotate D.length T.anti)) ∧
      Edge H v (T.lateral ((finRotate D.length).symm T.anti)) := by
  have hjop := T.partner_facet_eq_opposite hP hG hn hvG hH hm hvH hGH j hHK
  subst j
  have hv := hG.1.2.extremePoints_subset_extremePoints hvG
  obtain ⟨c, d, he, hcH, hdH, _⟩ := unitUniform5_polygon_vertexFigure_edge hP hv hH hvH.1
  have hcd := he.2.2.1
  have hK := (D.facet_incidence T.opposite).1
  have hHf : IsConvexFace (D.facet T.opposite) H := face_restrict hH.1 hK.1.2.1 hHK
  have hKfin := uniform_finitePolytope (D.facet_unitUniform hP T.opposite).1
  have hcK := (edge_face_iff hKfin hHf hvH.1 hcH.2.1.1).mpr hcH
  have hdK := (edge_face_iff hKfin hHf hvH.1 hdH.2.1.1).mpr hdH
  have hdist : dist c d = CaseB.chord m := polygonFace_neighbor_chord hP hH hcH hdH hcd
  have hch : CaseB.chord m ≠ Real.sqrt 2 := by
    intro hh
    have heq := (CaseB.case_chord_nat_eq_sqrt_two_iff (by omega : 3 ≤ m)).mp hh
    omega
  have hcross0 : dist T.base.a (T.lateral (finRotate D.length T.anti)) = Real.sqrt 2 ∧
      dist T.base.b (T.lateral (finRotate D.length T.anti)) = Real.sqrt 2 := by
    have ha := T.first.apex_a
    have hb := T.first.apex_b
    rw [T.first_base, T.first_apex] at ha hb
    exact ⟨ha, hb⟩
  have hcross1 : dist T.base.a (T.lateral ((finRotate D.length).symm T.anti)) = Real.sqrt 2 ∧
      dist T.base.b (T.lateral ((finRotate D.length).symm T.anti)) = Real.sqrt 2 := by
    have ha := T.last.apex_a
    have hb := T.last.apex_b
    rw [T.last_base, T.last_apex] at ha hb
    exact ⟨ha, hb⟩
  have hi : T.opposite ∈ D.slotsAwayFrom T.anti := by rw [T.away]; simp
  have hneighbors : ∀ w, Edge (D.facet T.opposite) v w ↔
      w = T.base.a ∨ w = T.base.b ∨ w = T.lateral (finRotate D.length T.anti) ∨
      w = T.lateral ((finRotate D.length).symm T.anti) := by
    have hh := T.duoprism_slot_neighbors hP hG hn hvG _ hi
    simpa only [T.opposite_eq, (finRotate_three_orbit T.length_three T.anti).2.1] using hh
  have hab : T.base.a ≠ T.base.b := fun he => by
    have hh := T.points_injective hG (by omega : 3 ≤ n) (show T.points 0 = T.points 1 from he)
    exact (by decide : (0 : Fin 6) ≠ 1) hh
  have haG := (T.base.polygon_neighbors T.base.a).mpr (Or.inl rfl)
  have hbG := (T.base.polygon_neighbors T.base.b).mpr (Or.inr rfl)
  have hc : c ≠ T.base.a ∧ c ≠ T.base.b := by
    constructor
    · intro hca
      subst c
      rcases (hneighbors d).mp hdK with hda | hdb | hd0 | hd1
      · exact hcd hda.symm
      · subst d
        exact hGH (polygonFace_eq_of_common_neighbor_pair hG hH haG hbG hcH hdH hab)
      · exact hch (hdist.symm.trans (hd0 ▸ hcross0.1))
      · exact hch (hdist.symm.trans (hd1 ▸ hcross1.1))
    · intro hcb
      subst c
      rcases (hneighbors d).mp hdK with hda | hdb | hd0 | hd1
      · subst d
        exact hGH (polygonFace_eq_of_common_neighbor_pair hG hH haG hbG hdH hcH hab)
      · exact hcd hdb.symm
      · exact hch (hdist.symm.trans (hd0 ▸ hcross0.2))
      · exact hch (hdist.symm.trans (hd1 ▸ hcross1.2))
  have hd : d ≠ T.base.a ∧ d ≠ T.base.b := by
    constructor
    · intro hda
      subst d
      rcases (hneighbors c).mp hcK with hca | hcb | hc0 | hc1
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
      rcases (hneighbors c).mp hcK with hca | hcb | hc0 | hc1
      · exact hc.1 hca
      · exact hc.2 hcb
      · apply hch
        rw [← hdist, hc0, dist_comm]
        exact hcross0.2
      · apply hch
        rw [← hdist, hc1, dist_comm]
        exact hcross1.2
  have hcp : c = T.lateral (finRotate D.length T.anti) ∨ c = T.lateral ((finRotate D.length).symm T.anti) := by
    rcases (hneighbors c).mp hcK with hh | hh | hh | hh
    · exact (hc.1 hh).elim
    · exact (hc.2 hh).elim
    · exact Or.inl hh
    · exact Or.inr hh
  have hdp : d = T.lateral (finRotate D.length T.anti) ∨ d = T.lateral ((finRotate D.length).symm T.anti) := by
    rcases (hneighbors d).mp hdK with hh | hh | hh | hh
    · exact (hd.1 hh).elim
    · exact (hd.2 hh).elim
    · exact Or.inl hh
    · exact Or.inr hh
  have hedge : Edge H v (T.lateral (finRotate D.length T.anti)) ∧ Edge H v (T.lateral ((finRotate D.length).symm T.anti)) := by
    rcases hcp with rfl | rfl <;> rcases hdp with rfl | rfl
    · exact (hcd rfl).elim
    · exact ⟨hcH, hdH⟩
    · exact ⟨hdH, hcH⟩
    · exact (hcd rfl).elim
  exact hedge

end Uniform5.Composition.TypeIIActualFanData
