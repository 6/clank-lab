import Uniform5.CompositionWedgeTypeIIShape
import Uniform5.CompositionWedgeTypeIIIIncidence

/-! All vertices and whole facets of the Type II W instance are actual
vertex-figure vertices and sections of actual incident facets. -/
noncomputable section
namespace Uniform5.Composition.TypeIIActualFanData
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
  (T : TypeIIActualFanData D v n)

theorem points_parent_neighbors (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) : ∀ i, Edge P v (T.points i) := by
  intro i
  have hi : T.points i ∈ Set.range T.points := ⟨i, rfl⟩
  rw [T.points_range_fan_neighbors hP hG hn hv] at hi
  obtain ⟨j, he⟩ := hi
  exact (edge_face_iff (uniform_finitePolytope hP.1) (D.facet_incidence j).1.1
    he.1.1 he.2.1.1).mpr he

theorem wedgeShape_points (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ)
    {q : ℕ} (hq : 3 ≤ q)
    (hmodel : Congruent (D.facet T.opposite) (duoprismModel n q)) :
    ((T.wedgeShape hP hG hn hv hq hmodel).points : Set (Space 5)) ⊆
      (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ := by
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  rw [finitePolytope_unit_vertexFigure_extremePoints (uniform_finitePolytope hP.1)
    (hG.1.2.extremePoints_subset_extremePoints hv) _ (intrinsicRadius P) hs hP.2]
  intro x hx
  change x ∈ ({T.points 0,T.points 1,T.points 2,T.points 3,T.points 4,T.points 5} : Finset (Space 5)) at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact T.points_parent_neighbors hP hG hn hv _

theorem wedgeShape_facets (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ)
    {q : ℕ} (hq : 3 ≤ q)
    (hmodel : Congruent (D.facet T.opposite) (duoprismModel n q)) :
    ∀ B ∈ (T.wedgeShape hP hG hn hv hq hmodel).facets,
    ∃ K, Facet P K ∧ v ∈ K ∧ B = K ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) := by
  let rot := finRotate D.length
  let a := T.anti
  have hi : T.opposite ∈ D.slotsAwayFrom T.anti := by rw [T.away]; simp
  have hvK (j : Fin D.length) : v ∈ (D.facet j).extremePoints ℝ :=
    (face_restrict hG.1 (D.facet_incidence j).1.1.2.1 (D.facet_incidence j).2.1).2.extremePoints_subset_extremePoints hv
  intro B hB
  change B ∈ ({convexHull ℝ {T.base.a,T.base.b,T.base.x,T.base.y,T.lateral (rot a)},
    convexHull ℝ {T.base.a,T.base.b,T.base.x,T.base.y,T.lateral (rot.symm a)},
    convexHull ℝ {T.base.a,T.base.b,T.lateral (rot a),T.lateral (rot.symm a)}} : Set (Set (Space 5))) at hB
  rcases hB with hB | hB | hB
  · refine ⟨D.facet a, (D.facet_incidence _).1, (hvK a).1, ?_⟩
    rw [hB]
    symm
    exact actual_facet_figure_of_neighbors hP (D.facet_incidence _).1
      (D.facet_unitUniform hP _) (hvK _) _ T.first_neighbors
  · refine ⟨D.facet (rot.symm a), (D.facet_incidence _).1, (hvK _).1, ?_⟩
    rw [hB]
    symm
    exact actual_facet_figure_of_neighbors hP (D.facet_incidence _).1
      (D.facet_unitUniform hP _) (hvK _) _ T.last_neighbors
  · refine ⟨D.facet T.opposite, (D.facet_incidence _).1, (hvK _).1, ?_⟩
    rw [hB]
    symm
    apply actual_facet_figure_of_neighbors hP (D.facet_incidence _).1
      (D.facet_unitUniform hP _) (hvK _) _
    have he := T.duoprism_slot_neighbors hP hG hn hv _ hi
    simpa only [T.opposite_eq, (finRotate_three_orbit T.length_three T.anti).2.1] using he

end Uniform5.Composition.TypeIIActualFanData
