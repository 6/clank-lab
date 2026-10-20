import Uniform5.CompositionWedgeActualGeometry
import Uniform5.CompositionTypeIICoherentEdges
import Uniform5.CompositionDuoprismNeighborMetrics

/-! The literal six-point W shape is derived from actual Type II fan
geometry, retaining the actual opposite duoprism parameter. -/
noncomputable section
namespace Uniform5.Composition.TypeIIActualFanData
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
  (T : TypeIIActualFanData D v n)

theorem lateral_metric (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) (j : Fin D.length)
    (hj : j ∈ D.slotsAwayFrom T.anti) {q : ℕ} (hq : 3 ≤ q)
    (hmodel : Congruent (D.facet j) (duoprismModel n q)) :
    dist T.base.a (T.lateral j) = Real.sqrt 2 ∧
    dist T.base.b (T.lateral j) = Real.sqrt 2 ∧
    dist T.base.a (T.lateral (finRotate D.length j)) = Real.sqrt 2 ∧
    dist T.base.b (T.lateral (finRotate D.length j)) = Real.sqrt 2 ∧
    dist (T.lateral j) (T.lateral (finRotate D.length j)) = CaseB.chord q := by
  obtain ⟨hja, hrja⟩ := (D.slotsAwayFrom_mem T.anti j).mp hj
  have hGK : PolygonFace (D.facet j) G n :=
    ⟨face_restrict hG.1 (D.facet_incidence j).1.1.2.1 (D.facet_incidence j).2.1, hG.2⟩
  obtain ⟨U⟩ := unitUniform4_duoprism_neighbor_chart_parameters (D.facet_unitUniform hP j)
    (by omega) hq hmodel hGK (by omega) hv
  have hlat : Edge (D.facet j) v (T.lateral j) :=
    (T.duoprism_slot_neighbors hP hG hn hv j hj _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hnxt : Edge (D.facet j) v (T.lateral (finRotate D.length j)) :=
    (T.duoprism_slot_neighbors hP hG hn hv j hj _).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have ha := (T.base.polygon_neighbors _).mpr (Or.inl rfl)
  have hb := (T.base.polygon_neighbors _).mpr (Or.inr rfl)
  refine ⟨U.polygon_lateral_dist ha hlat (T.lateral_outside j hja),
    U.polygon_lateral_dist hb hlat (T.lateral_outside j hja),
    U.polygon_lateral_dist ha hnxt (T.lateral_outside _ hrja),
    U.polygon_lateral_dist hb hnxt (T.lateral_outside _ hrja),
    U.lateral_dist hlat hnxt (T.lateral_outside j hja) (T.lateral_outside _ hrja) ?_⟩
  exact D.cell_lateral_points_injective hG
    (fun he => (finRotate_ne_and_twice_ne D.length_ge j).1 he.symm)
    (T.lateral_mem j hja) (T.lateral_mem _ hrja) (T.lateral_outside j hja)

noncomputable def wedgeShape (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ)
    {q : ℕ} (hq : 3 ≤ q)
    (hmodel : Congruent (D.facet T.opposite) (duoprismModel n q)) :
    Wedge.TypeIIShape (some (n : ℝ)) (some (q : ℝ)) where
  a := T.base.a
  b := T.base.b
  x := T.base.x
  y := T.base.y
  ab := T.base.chord_ab
  xy := T.base.side_xy
  ax := T.base.side_ax
  by_ := T.base.side_by
  ay := T.base.diagonal_ay
  bx := T.base.diagonal_bx
  z₁ := T.lateral (finRotate D.length T.anti)
  z₂ := T.lateral ((finRotate D.length).symm T.anti)
  apex_distances := by
    intro z hz p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hp
    have hfa := T.first.apex_a
    have hfb := T.first.apex_b
    have hfx := T.first.apex_x
    have hfy := T.first.apex_y
    have hla := T.last.apex_a
    have hlb := T.last.apex_b
    have hlx := T.last.apex_x
    have hly := T.last.apex_y
    rw [T.first_base, T.first_apex] at hfa hfb hfx hfy
    rw [T.last_base, T.last_apex] at hla hlb hlx hly
    rcases hz with rfl | rfl <;> rcases hp with rfl | rfl | rfl | rfl
    all_goals assumption
  partner_chord := by
    have hi : T.opposite ∈ D.slotsAwayFrom T.anti := by rw [T.away]; simp
    have hh := (T.lateral_metric hP hG hn hv T.opposite hi hq hmodel).2.2.2.2
    simpa only [T.opposite_eq, (finRotate_three_orbit T.length_three T.anti).2.1] using hh

end Uniform5.Composition.TypeIIActualFanData
