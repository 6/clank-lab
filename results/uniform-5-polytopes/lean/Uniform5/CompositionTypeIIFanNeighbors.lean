import Uniform5.CompositionSimpleFacetNeighborCover
import Uniform5.CompositionSingleFanCover
import Uniform5.CompositionAntiprismCellSlices

/-! Every actual neighbor in a Type II single-polygon fan lies in one
of its two antiprism-prism facets. -/
noncomputable section
namespace Uniform5.Composition
open Set

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

theorem cell_facet (hP : UnitUniform 5 P) {n : ℕ} (hG : PolygonFace P G n)
    (j : Fin D.length) : Facet (D.facet j) (D.cell j) := by
  refine ⟨face_restrict (D.cell_face j) (D.facet_incidence j).1.1.2.1
    (D.facet_incidence j).2.2.1,
    (polygonFace_nonempty hG).mono (D.cell_contains j), ?_⟩
  rw [D.cell_dimension, uniform_dimension (D.facet_unitUniform hP j).1]

theorem next_cell_facet (hP : UnitUniform 5 P) {n : ℕ} (hG : PolygonFace P G n)
    (j : Fin D.length) : Facet (D.facet j) (D.cell (finRotate D.length j)) := by
  rw [cycle_apply_finRotate (by have := D.length_ge; omega) D.cell D.cell_closed j]
  refine ⟨face_restrict (D.cell_face _) (D.facet_incidence j).1.1.2.1
    (D.facet_incidence j).2.2.2,
    (polygonFace_nonempty hG).mono (D.cell_contains _), ?_⟩
  rw [D.cell_dimension, uniform_dimension (D.facet_unitUniform hP j).1]

theorem cell_facet_of_not_away (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (a j : Fin D.length) (hj : j ∉ D.slotsAwayFrom a) :
    Facet (D.facet j) (D.cell a) := by
  have hh : j = a ∨ finRotate D.length j = a := by
    simpa only [slotsAwayFrom_mem, not_and_or, not_not] using hj
  rcases hh with rfl | hh
  · exact D.cell_facet hP hG _
  · rw [← hh]; exact D.next_cell_facet hP hG j

theorem typeII_neighbor_antiprism_facet
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    {v w : Space 5} (hvG : v ∈ G.extremePoints ℝ) (hu : UniqueLargeFaceAt P v G)
    (hlen : D.length = 3) (a i : Fin D.length) (q : ℕ) (hq : 3 ≤ q)
    (hi : D.slotsAwayFrom a = {i})
    (hduo : Congruent (D.facet i) (duoprismModel n q)) (he : Edge P v w) :
    ∃ j : Fin D.length, j ∉ D.slotsAwayFrom a ∧ w ∈ D.facet j := by
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have hwV : w ∈ (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ := by
    rw [finitePolytope_unit_vertexFigure_extremePoints
      (uniform_finitePolytope hP.1) he.1 _ (intrinsicRadius P) hs hP.2]
    exact he
  obtain ⟨j, hwj⟩ := unitUniform5_single_fan_vertex_cover
    classification3D classification4D N S hLIB hS1 hB2 hP hG hn he.1 hu D hwV
  by_cases hj : j ∉ D.slotsAwayFrom a
  · exact ⟨j, hj, hwj.1.1⟩
  have hji : j = i := by simpa [hi] using not_not.mp hj
  subst j
  have hia : i ∈ D.slotsAwayFrom a := by rw [hi]; simp
  have hne := (D.slotsAwayFrom_mem a i).mp hia
  obtain ⟨hai, hiaa⟩ := finRotate_three_other hlen a i hne.1 hne.2
  have hvK : v ∈ D.facet i := (D.facet_incidence i).2.1 hvG.1
  have heK := (edge_face_iff (uniform_finitePolytope hP.1)
    (D.facet_incidence i).1.1 hvK hwj.1.1).mp he
  have hGK : PolygonFace (D.facet i) G n :=
    ⟨face_restrict hG.1 (D.facet_incidence i).1.1.2.1 (D.facet_incidence i).2.1, hG.2⟩
  obtain ⟨T⟩ := unitUniform4_duoprism_neighbor_chart_parameters (D.facet_unitUniform hP i)
    (by omega : 3 ≤ n) hq hduo hGK (by omega : n ≠ 4) hvG
  have hcn : D.cell i ≠ D.cell (finRotate D.length i) := by
    rw [cycle_apply_finRotate (by have := D.length_ge; omega) D.cell D.cell_closed i]
    exact cell_cycle_consecutive_ne D.length_ge D.cell D.cell_closed D.cell_injective i.isLt
  rcases finitePolytope_simpleVertex_two_facets_cover
    (uniform_finitePolytope (D.facet_unitUniform hP i).1)
    (uniform_dimension (D.facet_unitUniform hP i).1) heK.1
    (T.neighbour_card (D.facet_unitUniform hP i) heK.1)
    (D.cell_facet hP hG i) (D.next_cell_facet hP hG i)
    (D.cell_contains i hvG.1) (D.cell_contains _ hvG.1) hcn heK with hw | hw
  · refine ⟨a, ?_, ?_⟩
    · simp [slotsAwayFrom]
    · have hh := (D.next_cell_facet hP hG a).1.2.1
      rw [hai] at hh
      exact hh hw
  · refine ⟨finRotate D.length i, ?_, (D.facet_incidence _).2.2.1 hw⟩
    rw [D.slotsAwayFrom_mem, hiaa]
    simp

/-- The whole selected antiprism cell, rather than only its tangent
trapezoid, transports orthogonally to a cell containing each root neighbor. -/
theorem typeII_root_cell_translates
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ) (hu : UniqueLargeFaceAt P v G)
    (hII : D.CaseBTypeII n) :
    ∃ a : Fin D.length, Congruent (D.cell a) (antiprismModel n) ∧
      ∀ w, Edge P v w → ∃ d ∈ CaseB.normals (D.cell a),
        IsConvexFace P (CaseB.translate (D.cell a) d) ∧
        affineDimension (CaseB.translate (D.cell a) d) = 3 ∧
        Congruent (CaseB.translate (D.cell a) d) (antiprismModel n) ∧
        w ∈ CaseB.translate (D.cell a) d := by
  obtain ⟨hlen, a, i, q, hq, ha, hi, _, hanti, hduo⟩ := hII
  refine ⟨a, ha, ?_⟩
  intro w he
  obtain ⟨j, hj, hw⟩ := D.typeII_neighbor_antiprism_facet classification3D classification4D
    N S hLIB hS1 hB2 hP hG hn hvG hu hlen a i q hq hi hduo he
  have hK := (D.facet_incidence j).1
  have hGK : PolygonFace (D.facet j) G n :=
    ⟨face_restrict hG.1 hK.1.2.1 (D.facet_incidence j).2.1, hG.2⟩
  have hwK : w ∈ (D.facet j).extremePoints ℝ := by
    rw [face_extremePoints_eq hK.1]
    exact ⟨hw, he.2.1⟩
  obtain ⟨d, hd, hF, hFA, hwF⟩ := unitUniform4_antiprismPrism_cell_translate
    (D.facet_unitUniform hP j) (by omega : 5 ≤ n) (hanti j hj) hGK
    (D.cell_facet_of_not_away hP hG a j hj) (D.cell_contains a) ha hwK
  refine ⟨d, hd, ⟨hF.1.1, hK.1.2.trans hF.1.2⟩, ?_, hFA, hwF⟩
  have hdim := hF.2.2
  rw [uniform_dimension (D.facet_unitUniform hP j).1] at hdim
  omega

end ActualPolygonCycle
end Uniform5.Composition
