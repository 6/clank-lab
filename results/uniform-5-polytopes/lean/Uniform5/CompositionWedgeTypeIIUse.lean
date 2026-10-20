import Uniform5.CompositionWedgeTypeIIIncidence
import Uniform5.CompositionWedgeActualUse

/-! Apply the named W computation to every actual Type II fan.
The small opposite parameter protects only the base edge; a large
opposite parameter also protects the two actual pyramid apices. -/
noncomputable section
namespace Uniform5.Composition.TypeIIActualFanData
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
  (T : TypeIIActualFanData D v n)

theorem wedge_unpaired_only_edge (p1 : CaseB.P1) (hW : Wedge.W p1)
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hv : v ∈ G.extremePoints ℝ) {q : ℕ} (hq : 3 ≤ q) (hsmall : q ≤ 16)
    (hmodel : Congruent (D.facet T.opposite) (duoprismModel n q))
    {x y : Space 5} (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y)
    (hlong : CaseB.chord 17 ≤ dist x y) : Wedge.pair T.base.a T.base.b x y := by
  let S := T.wedgeShape hP hG hn hv hq hmodel
  let F := Wedge.actualGeometry hP v S.points {S.a,S.b} (Wedge.pair S.a S.b) S.facets
  have hvP := hG.1.2.extremePoints_subset_extremePoints hv
  have hpoints := T.wedgeShape_points hP hG hn hv hq hmodel
  have hfacets := T.wedgeShape_facets hP hG hn hv hq hmodel
  have hfinite : Wedge.finiteParameters (some (n : ℝ)) (.unpairedII q) := by
    simp [Wedge.finiteParameters, Wedge.atInfinity]
  have hreal : Wedge.RealizesWFan p1 (some (n : ℝ)) (.unpairedII q) F := by
    refine ⟨hfinite, S, ?_⟩
    apply Wedge.actualGeometry_realizes hP hvP _ _ _ _ hfinite hpoints _ hfacets
    refine ⟨S.a, by simp [S, Wedge.TypeIIShape.points], S.b,
      by simp [S, Wedge.TypeIIShape.points], ?_⟩
    rw [S.ab]
    change 1 < CaseB.chord n
    have hm := CaseB.chord_mono (by norm_num : (3 : ℝ) ≤ 17)
      (by exact_mod_cast hn : (17 : ℝ) ≤ n)
    linarith [CaseB.chord_seventeen_gt]
  apply Wedge.actual_only_protected_edges p1 hW (by change (17 : ℝ) ≤ n; exact_mod_cast hn)
    (show CaseB.WListed p1 (some (n : ℝ)) (.unpairedII q) from ⟨hq,hsmall⟩)
    F hreal hP hvP (Wedge.pair T.base.a T.base.b) (fun _ _ => False)
    Wedge.pair_symm _ _ (fun _ _ h => Or.inl h) (fun _ _ h => h.elim) he hlong
  · intro z hz
    change z ∈ ({S.a,S.b} : Finset (Space 5)) at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    have ha : S.a ∈ S.points := by simp [S, Wedge.TypeIIShape.points]
    have hb : S.b ∈ S.points := by simp [S, Wedge.TypeIIShape.points]
    have hab : CaseB.chord 17 ≤ dist S.a S.b := by
      rw [S.ab]
      exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hn)
    rcases hz with rfl | rfl
    · exact ⟨S.b,hpoints hb,Or.inl ⟨rfl,rfl⟩,hab⟩
    · exact ⟨S.a,hpoints ha,Or.inr ⟨rfl,rfl⟩,by simpa only [dist_comm] using hab⟩
  · exact Wedge.actualGeometry_coverage hP hvP _ _ _ _ hpoints hfacets

theorem wedge_paired_only_two_edges (p1 : CaseB.P1) (hW : Wedge.W p1)
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hv : v ∈ G.extremePoints ℝ) {q : ℕ} (hq : 17 ≤ q)
    (hmodel : Congruent (D.facet T.opposite) (duoprismModel n q))
    {x y : Space 5} (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y)
    (hlong : CaseB.chord 17 ≤ dist x y) :
    Wedge.pair T.base.a T.base.b x y ∨
      Wedge.pair (T.lateral (finRotate D.length T.anti))
        (T.lateral ((finRotate D.length).symm T.anti)) x y := by
  let S := T.wedgeShape hP hG hn hv (by omega : 3 ≤ q) hmodel
  let E := fun x y => Wedge.pair S.a S.b x y ∨ Wedge.pair S.z₁ S.z₂ x y
  let F := Wedge.actualGeometry hP v S.points {S.a,S.b,S.z₁,S.z₂} E S.facets
  have hvP := hG.1.2.extremePoints_subset_extremePoints hv
  have hpoints := T.wedgeShape_points hP hG hn hv (by omega : 3 ≤ q) hmodel
  have hfacets := T.wedgeShape_facets hP hG hn hv (by omega : 3 ≤ q) hmodel
  have hfinite : Wedge.finiteParameters (some (n : ℝ)) (.pairedII (some (q : ℝ))) := by
    simp [Wedge.finiteParameters, Wedge.atInfinity]
  have hreal : Wedge.RealizesWFan p1 (some (n : ℝ)) (.pairedII (some (q : ℝ))) F := by
    refine ⟨hfinite, S, ?_⟩
    apply Wedge.actualGeometry_realizes hP hvP _ _ _ _ hfinite hpoints _ hfacets
    refine ⟨S.a, by simp [S, Wedge.TypeIIShape.points], S.b,
      by simp [S, Wedge.TypeIIShape.points], ?_⟩
    rw [S.ab]
    change 1 < CaseB.chord n
    have hm := CaseB.chord_mono (by norm_num : (3 : ℝ) ≤ 17)
      (by exact_mod_cast hn : (17 : ℝ) ≤ n)
    linarith [CaseB.chord_seventeen_gt]
  have hsymm {x y : Space 5} (h : E x y) : E y x :=
    h.elim (fun hh => Or.inl (Wedge.pair_symm hh)) (fun hh => Or.inr (Wedge.pair_symm hh))
  apply Wedge.actual_only_protected_edges p1 hW (by change (17 : ℝ) ≤ n; exact_mod_cast hn)
    (show CaseB.WListed p1 (some (n : ℝ)) (.pairedII (some (q : ℝ))) from
      (by change (17 : ℝ) ≤ q; exact_mod_cast hq))
    F hreal hP hvP E (fun _ _ => False) hsymm _ _
    (fun _ _ h => Or.inl h) (fun _ _ h => h.elim) he hlong
  · intro z hz
    change z ∈ ({S.a,S.b,S.z₁,S.z₂} : Finset (Space 5)) at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    have ha : S.a ∈ S.points := by simp [S, Wedge.TypeIIShape.points]
    have hb : S.b ∈ S.points := by simp [S, Wedge.TypeIIShape.points]
    have hc : S.z₁ ∈ S.points := by simp [S, Wedge.TypeIIShape.points]
    have hd : S.z₂ ∈ S.points := by simp [S, Wedge.TypeIIShape.points]
    have hab : CaseB.chord 17 ≤ dist S.a S.b := by
      rw [S.ab]
      exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hn)
    have hcd : CaseB.chord 17 ≤ dist S.z₁ S.z₂ := by
      rw [S.partner_chord]
      exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hq)
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨S.b,hpoints hb,Or.inl (Or.inl ⟨rfl,rfl⟩),hab⟩
    · exact ⟨S.a,hpoints ha,Or.inl (Or.inr ⟨rfl,rfl⟩),by simpa only [dist_comm] using hab⟩
    · exact ⟨S.z₂,hpoints hd,Or.inr (Or.inl ⟨rfl,rfl⟩),hcd⟩
    · exact ⟨S.z₁,hpoints hc,Or.inr (Or.inr ⟨rfl,rfl⟩),by simpa only [dist_comm] using hcd⟩
  · exact Wedge.actualGeometry_coverage hP hvP _ _ _ _ hpoints hfacets

/-- The actual Type II fan has at most its two displayed long edges. -/
theorem long_edges_two_pairs (p1 : CaseB.P1) (hW : Wedge.W p1)
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hv : v ∈ G.extremePoints ℝ) {x y : Space 5}
    (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y)
    (hlong : CaseB.chord 17 ≤ dist x y) :
    Wedge.pair T.base.a T.base.b x y ∨ Wedge.pair T.first.apex T.last.apex x y := by
  rw [T.first_apex, T.last_apex]
  obtain ⟨q,hq,hmodel⟩ := T.duoprism
  by_cases hsmall : q ≤ 16
  · exact Or.inl (T.wedge_unpaired_only_edge p1 hW hP hG hn hv hq hsmall hmodel he hlong)
  · exact T.wedge_paired_only_two_edges p1 hW hP hG hn hv (by omega) hmodel he hlong

theorem opposite_contains_apexes (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) :
    T.first.apex ∈ D.facet T.opposite ∧ T.last.apex ∈ D.facet T.opposite := by
  have hi : T.opposite ∈ D.slotsAwayFrom T.anti := by rw [T.away]; simp
  have he := T.duoprism_slot_neighbors hP hG hn hv _ hi
  have hfirst := ((he _).mpr (Or.inr (Or.inr (Or.inl rfl)))).2.1.1
  have hlast := ((he _).mpr (Or.inr (Or.inr (Or.inr rfl)))).2.1.1
  rw [T.first_apex, T.last_apex]
  simpa only [T.opposite_eq, (finRotate_three_orbit T.length_three T.anti).2.1] using
    And.intro hfirst hlast

end Uniform5.Composition.TypeIIActualFanData
