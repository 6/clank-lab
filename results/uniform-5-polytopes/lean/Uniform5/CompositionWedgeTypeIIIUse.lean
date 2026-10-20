import Uniform5.CompositionWedgeTypeIIIIncidence
import Uniform5.CompositionWedgeActualUse
import Uniform5.CompositionPolygonFanMembership

/-! Actual Type III fans have only the original long edge. Therefore the
single-large-face condition follows from W, rather than being assumed. -/
noncomputable section
namespace Uniform5.Composition.TypeIIIActualFanData
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
  (T : TypeIIIActualFanData D v n)

theorem wedge_only_edge (p1 : CaseB.P1) (hW : Wedge.W p1)
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hv : v ∈ G.extremePoints ℝ) {x y : Space 5}
    (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y)
    (hlong : CaseB.chord 17 ≤ dist x y) : Wedge.pair T.base.a T.base.b x y := by
  obtain ⟨q,r,hq,hr,hpair,hfirst,hsecond⟩ := T.duoprism_pair
  let S := T.wedgeShape hP hG hn hv hq hr hfirst hsecond
  let F := Wedge.actualGeometry hP v S.points {S.a,S.b} (Wedge.pair S.a S.b) S.facets
  have hvP := hG.1.2.extremePoints_subset_extremePoints hv
  have hpoints := T.wedgeShape_points hP hG hn hv hq hr hfirst hsecond
  have hfacets := T.wedgeShape_facets hP hG hn hv hq hr hfirst hsecond
  have hfinite : Wedge.finiteParameters (some (n : ℝ)) (.unpairedIII q r) := by
    simp [Wedge.finiteParameters, Wedge.atInfinity]
  have hreal : Wedge.RealizesWFan p1 (some (n : ℝ)) (.unpairedIII q r) F := by
    refine ⟨hfinite, S, ?_⟩
    apply Wedge.actualGeometry_realizes hP hvP _ _ _ _ hfinite hpoints _ hfacets
    refine ⟨S.a, by simp [S, Wedge.TypeIIIShape.points], S.b,
      by simp [S, Wedge.TypeIIIShape.points], ?_⟩
    rw [S.ab]
    change 1 < CaseB.chord n
    have hm := CaseB.chord_mono (by norm_num : (3 : ℝ) ≤ 17)
      (by exact_mod_cast hn : (17 : ℝ) ≤ n)
    linarith [CaseB.chord_seventeen_gt]
  apply Wedge.actual_only_protected_edges p1 hW (by change (17 : ℝ) ≤ n; exact_mod_cast hn)
    (show CaseB.WListed p1 (some (n : ℝ)) (.unpairedIII q r) from hpair) F hreal hP hvP (Wedge.pair T.base.a T.base.b) (fun _ _ => False)
    Wedge.pair_symm _ _ (fun _ _ h => Or.inl h) (fun _ _ h => h.elim) he hlong
  · intro z hz
    change z ∈ ({S.a,S.b} : Finset (Space 5)) at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    have ha : S.a ∈ S.points := by simp [S, Wedge.TypeIIIShape.points]
    have hb : S.b ∈ S.points := by simp [S, Wedge.TypeIIIShape.points]
    have hab : CaseB.chord 17 ≤ dist S.a S.b := by
      rw [S.ab]
      exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hn)
    rcases hz with rfl | rfl
    · exact ⟨S.b,hpoints hb,Or.inl ⟨rfl,rfl⟩,hab⟩
    · exact ⟨S.a,hpoints ha,Or.inr ⟨rfl,rfl⟩,by simpa only [dist_comm] using hab⟩
  · exact Wedge.actualGeometry_coverage hP hvP _ _ _ _ hpoints hfacets

include T in
/-- The uniqueness needed by the Type III case analysis is a conclusion
of the named W computation on the actual fan. -/
theorem uniqueLargeFaceAt (p1 : CaseB.P1) (hW : Wedge.W p1)
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hv : v ∈ G.extremePoints ℝ) : UniqueLargeFaceAt P v G := by
  intro H m hH hm hvH
  have hvP := hG.1.2.extremePoints_subset_extremePoints hv
  obtain ⟨x,y,he,hx,hy,_⟩ := unitUniform5_polygon_vertexFigure_edge hP hvP hH hvH.1
  have hlong : CaseB.chord 17 ≤ dist x y := by
    rw [polygonFace_neighbor_chord hP hH hx hy he.2.2.1]
    exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hm)
  have hp := T.wedge_only_edge p1 hW hP hG hn hv he hlong
  have ha := (T.base.polygon_neighbors _).mpr (Or.inl rfl)
  have hb := (T.base.polygon_neighbors _).mpr (Or.inr rfl)
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact polygonFace_eq_of_common_neighbor_pair hH hG hx hy ha hb he.2.2.1
  · exact polygonFace_eq_of_common_neighbor_pair hH hG hx hy hb ha he.2.2.1

end Uniform5.Composition.TypeIIIActualFanData
