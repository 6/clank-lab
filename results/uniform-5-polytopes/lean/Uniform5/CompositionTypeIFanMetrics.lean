import Uniform5.CompositionTypeIFanChart
import Uniform5.CompositionDuoprismNeighborMetrics

/-! Exact F3 distances for the coherently labelled actual Type I fan. -/
noncomputable section
namespace Uniform5.Composition.TypeIFanChart
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

theorem cross_dist (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hvG : v ∈ G.extremePoints ℝ)
    (i : Fin D.length) {q : ℕ} (hq : 3 ≤ q)
    (hmodel : Congruent (D.facet i) (duoprismModel n q)) :
    dist T.a (T.lateral i) = Real.sqrt 2 ∧ dist T.b (T.lateral i) = Real.sqrt 2 := by
  have hGF : PolygonFace (D.facet i) G n :=
    ⟨face_restrict hG.1 (D.facet_incidence i).1.1.2.1 (D.facet_incidence i).2.1, hG.2⟩
  obtain ⟨U⟩ := unitUniform4_duoprism_neighbor_chart_parameters (D.facet_unitUniform hP i)
    hn hq hmodel hGF hn4 hvG
  have hz := (T.facet_neighbors i (T.lateral i)).mpr (Or.inr (Or.inr (Or.inl rfl)))
  exact ⟨U.polygon_lateral_dist ((T.polygon_neighbors T.a).mpr (Or.inl rfl)) hz
      (T.lateral_outside i),
    U.polygon_lateral_dist ((T.polygon_neighbors T.b).mpr (Or.inr rfl)) hz (T.lateral_outside i)⟩

theorem lateral_dist (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hvG : v ∈ G.extremePoints ℝ)
    (i : Fin D.length) {q : ℕ} (hq : 3 ≤ q)
    (hmodel : Congruent (D.facet i) (duoprismModel n q)) :
    dist (T.lateral i) (T.lateral (finRotate D.length i)) = CaseB.chord q := by
  have hGF : PolygonFace (D.facet i) G n :=
    ⟨face_restrict hG.1 (D.facet_incidence i).1.1.2.1 (D.facet_incidence i).2.1, hG.2⟩
  obtain ⟨U⟩ := unitUniform4_duoprism_neighbor_chart_parameters (D.facet_unitUniform hP i)
    hn hq hmodel hGF hn4 hvG
  apply U.lateral_dist
    ((T.facet_neighbors i _).mpr (Or.inr (Or.inr (Or.inl rfl))))
    ((T.facet_neighbors i _).mpr (Or.inr (Or.inr (Or.inr rfl))))
    (T.lateral_outside i) (T.lateral_outside _)
  intro he
  exact (finRotate_ne_and_twice_ne D.length_ge i).1 (T.lateral_injective he).symm

end Uniform5.Composition.TypeIFanChart
