import Uniform5.CompositionWedgeTypeIIIShape

/-! Every literal vertex and whole facet in the Type III W chart comes
from the actual polytope, with no single-large-polygon hypothesis. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem actual_facet_figure_of_neighbors {P K : Set (Space 5)}
    (hP : UnitUniform 5 P) (hK : Facet P K) (hKU : UnitUniform 4 K)
    {v : Space 5} (hvK : v ∈ K.extremePoints ℝ) (points : Set (Space 5))
    (hN : ∀ w, Edge K v w ↔ w ∈ points) :
    K ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) =
      convexHull ℝ points := by
  rw [uniform_vertexFigure_face_inter hP.1 hK.1 hK.2.1 hvK.1]
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hKU.1
  rw [finitePolytope_unit_vertexFigure (uniform_finitePolytope hKU.1) hvK _
    (intrinsicRadius K) hs hKU.2]
  congr 1
  ext w
  exact hN w

namespace TypeIIIActualFanData
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
  (T : TypeIIIActualFanData D v n)

theorem points_parent_neighbors (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) : ∀ i, Edge P v (T.points i) := by
  let a := T.anti
  let rot := finRotate D.length
  have hra := (finRotate_ne_and_twice_ne D.length_ge a).1
  have hrra := (finRotate_four_orbit T.length_four a).1
  have hj : rot a ∈ D.slotsAwayFrom a := (D.slotsAwayFrom_mem a _).mpr ⟨hra, hrra⟩
  have lift (j : Fin D.length) (w : Space 5) (he : Edge (D.facet j) v w) : Edge P v w :=
    (edge_face_iff (uniform_finitePolytope hP.1) (D.facet_incidence j).1.1 he.1.1 he.2.1.1).mpr he
  intro i
  fin_cases i
  · exact lift a _ ((T.first_neighbors _).mpr (Or.inl rfl))
  · exact lift a _ ((T.first_neighbors _).mpr (Or.inr (Or.inl rfl)))
  · exact lift a _ ((T.first_neighbors _).mpr (Or.inr (Or.inr (Or.inl rfl))))
  · exact lift a _ ((T.first_neighbors _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact lift a _ ((T.first_neighbors _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  · exact lift (rot.symm a) _ ((T.last_neighbors _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  · exact lift (rot a) _ ((T.duoprism_slot_neighbors hP hG hn hv _ hj _).mpr
      (Or.inr (Or.inr (Or.inr rfl))))

theorem wedgeShape_points (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ)
    {q r : ℕ} (hq : 3 ≤ q) (hr : 3 ≤ r)
    (hfirst : Congruent (D.facet (finRotate D.length T.anti)) (duoprismModel n q))
    (hsecond : Congruent (D.facet (finRotate D.length (finRotate D.length T.anti)))
      (duoprismModel n r)) :
    ((T.wedgeShape hP hG hn hv hq hr hfirst hsecond).points : Set (Space 5)) ⊆
      (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ := by
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  rw [finitePolytope_unit_vertexFigure_extremePoints (uniform_finitePolytope hP.1)
    (hG.1.2.extremePoints_subset_extremePoints hv) _ (intrinsicRadius P) hs hP.2]
  intro x hx
  change x ∈ ({T.points 0,T.points 1,T.points 2,T.points 3,T.points 4,T.points 5,T.points 6} : Finset (Space 5)) at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact T.points_parent_neighbors hP hG hn hv _

theorem wedgeShape_facets (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ)
    {q r : ℕ} (hq : 3 ≤ q) (hr : 3 ≤ r)
    (hfirst : Congruent (D.facet (finRotate D.length T.anti)) (duoprismModel n q))
    (hsecond : Congruent (D.facet (finRotate D.length (finRotate D.length T.anti)))
      (duoprismModel n r)) :
    ∀ B ∈ (T.wedgeShape hP hG hn hv hq hr hfirst hsecond).facets,
    ∃ K, Facet P K ∧ v ∈ K ∧ B = K ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) := by
  let rot := finRotate D.length
  let a := T.anti
  have hra := (finRotate_ne_and_twice_ne D.length_ge a).1
  obtain ⟨hrra, hrrra, _⟩ := finRotate_four_orbit T.length_four a
  have hj : rot a ∈ D.slotsAwayFrom a := (D.slotsAwayFrom_mem a _).mpr ⟨hra,hrra⟩
  have hk : rot (rot a) ∈ D.slotsAwayFrom a := by
    apply (D.slotsAwayFrom_mem a _).mpr
    exact ⟨hrra, by change rot (rot (rot a)) ≠ a; rw [hrrra]; exact D.predecessor_ne a⟩
  have hvK (j : Fin D.length) : v ∈ (D.facet j).extremePoints ℝ :=
    (face_restrict hG.1 (D.facet_incidence j).1.1.2.1 (D.facet_incidence j).2.1).2.extremePoints_subset_extremePoints hv
  intro B hB
  change B ∈ ({convexHull ℝ {T.base.a,T.base.b,T.base.x,T.base.y,T.lateral (rot a)},
    convexHull ℝ {T.base.a,T.base.b,T.base.x,T.base.y,T.lateral (rot.symm a)},
    convexHull ℝ {T.base.a,T.base.b,T.lateral (rot a),T.lateral (rot (rot a))},
    convexHull ℝ {T.base.a,T.base.b,T.lateral (rot (rot a)),T.lateral (rot.symm a)}} : Set (Set (Space 5))) at hB
  rcases hB with hB | hB | hB | hB
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
  · refine ⟨D.facet (rot a), (D.facet_incidence _).1, (hvK _).1, ?_⟩
    rw [hB]
    symm
    exact actual_facet_figure_of_neighbors hP (D.facet_incidence _).1
      (D.facet_unitUniform hP _) (hvK _) _ (T.duoprism_slot_neighbors hP hG hn hv _ hj)
  · refine ⟨D.facet (rot (rot a)), (D.facet_incidence _).1, (hvK _).1, ?_⟩
    rw [hB]
    symm
    have he := T.duoprism_slot_neighbors hP hG hn hv _ hk
    rw [hrrra] at he
    exact actual_facet_figure_of_neighbors hP (D.facet_incidence _).1
      (D.facet_unitUniform hP _) (hvK _) _ he

end TypeIIIActualFanData
end Uniform5.Composition
