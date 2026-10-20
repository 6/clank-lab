import Uniform5.CompositionChartEdges
import Uniform5.CompositionAntiprismChart
import Uniform5.CompositionFigureRidgeCorrespondence
import Uniform5.CaseBCaseMetrics

/-! The cyclic trapezoid edge list is derived from actual convex geometry. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Exact edges at every vertex of the actual antiprism figure. The three
unit sides are exposed by separation; planar incidence forces the fourth
side and excludes both diagonals. -/
theorem AntiprismNeighborChart.figure_neighbors {A G : Set E} {v : E} {n : ℕ}
    (D : AntiprismNeighborChart A G v n) (hA : UnitUniform 3 A) (hn : 3 ≤ n)
    (hv : v ∈ A.extremePoints ℝ) :
    let B := vertexFigure A v (vertexCentroid (vertices A (uniform_finitePolytope hA.1)))
    (∀ z, Edge B D.a z ↔ z = D.b ∨ z = D.x) ∧
    (∀ z, Edge B D.b z ↔ z = D.a ∨ z = D.y) ∧
    (∀ z, Edge B D.x z ↔ z = D.a ∨ z = D.y) ∧
    (∀ z, Edge B D.y z ↔ z = D.b ∨ z = D.x) := by
  let hAP := uniform_finitePolytope hA.1
  let c := vertexCentroid (vertices A hAP)
  let B := vertexFigure A v c
  obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical hAP (uniform_vertexTransitive hA.1)
  have hB : FinitePolytope B := finitePolytope_vertexFigure_of_positiveDimension
    hAP hv c R hs hA.2 (by rw [uniform_dimension hA.1]; norm_num)
  have hBA : B ⊆ A := fun _ hx => hx.1
  have hself : A ∩ B = B := Set.inter_eq_right.mpr hBA
  have hdB : affineDimension B = 2 := by
    have hh := (unitUniform_vertexFigure_face_correspondence (n := 0) hA hv 2).1 A
      (finitePolytope_self_face hAP) hv.1 (by simpa using uniform_dimension hA.1)
    have hh' : affineDimension (A ∩ B) = 2 := hh.2.2
    rwa [hself] at hh'
  have hext : B.extremePoints ℝ = {D.a, D.b, D.x, D.y} := by
    rw [show B = vertexFigure A v c from rfl,
      finitePolytope_unit_vertexFigure_extremePoints hAP hv c R hs hA.2]
    ext z
    exact D.neighbors z
  have hpoints : ∀ z ∈ ({D.a, D.b, D.x, D.y} : Set E), z ∈ B ∧ z ∈ A.extremePoints ℝ := by
    intro z hz
    have hzB : z ∈ B.extremePoints ℝ := hext.symm ▸ hz
    refine ⟨hzB.1, ?_⟩
    have he : Edge A v z := (D.neighbors z).mpr hz
    exact he.2.1
  have hax : Edge B D.a D.x := unitUniform_convex_subset_unit_pair_edge hA
    (finitePolytope_convex hB) hBA (hpoints _ (by simp)).1 (hpoints _ (by simp)).1
    (hpoints _ (by simp)).2 (hpoints _ (by simp)).2 D.side_ax
  have hxy : Edge B D.x D.y := unitUniform_convex_subset_unit_pair_edge hA
    (finitePolytope_convex hB) hBA (hpoints _ (by simp)).1 (hpoints _ (by simp)).1
    (hpoints _ (by simp)).2 (hpoints _ (by simp)).2 D.side_xy
  have hby : Edge B D.b D.y := unitUniform_convex_subset_unit_pair_edge hA
    (finitePolytope_convex hB) hBA (hpoints _ (by simp)).1 (hpoints _ (by simp)).1
    (hpoints _ (by simp)).2 (hpoints _ (by simp)).2 D.side_by
  have hc : 0 < CaseB.chord n := CaseB.case_chord_pos (by exact_mod_cast hn)
  have hab : D.a ≠ D.b := by
    intro he
    have hh := D.chord_ab
    rw [he, dist_self] at hh
    linarith
  have hbx : D.b ≠ D.x := by
    intro he
    have hh := D.diagonal_bx
    rw [he, dist_self] at hh
    nlinarith
  have hay : D.a ≠ D.y := by
    intro he
    have hh := D.diagonal_ay
    rw [he, dist_self] at hh
    nlinarith
  exact planar_quadrilateral_chart_neighbors hB hdB
    (planar_quadrilateral_close_path hB hdB hext hax hxy hby hab hbx) hax hxy hby hbx hay

/-- The two cross-layer neighbors lie outside the chosen polygon as
actual points, so face-incidence uniqueness separates them from lateral
points in every different cell at that polygon. -/
theorem AntiprismNeighborChart.cross_not_mem_polygon {A G : Set E} {v : E} {n : ℕ}
    (D : AntiprismNeighborChart A G v n) (hA : UnitUniform 3 A) (hn : 3 ≤ n)
    (hG : IsConvexFace A G) : D.x ∉ G ∧ D.y ∉ G := by
  have hc : 0 < CaseB.chord n := CaseB.case_chord_pos (by exact_mod_cast hn)
  have hx := (D.neighbors D.x).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hy := (D.neighbors D.y).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hvG := ((D.polygon_neighbors D.a).mpr (Or.inl rfl)).1.1
  constructor
  · intro hxG
    have he := (D.polygon_neighbors D.x).mp
      ((edge_face_iff (uniform_finitePolytope hA.1) hG hvG hxG).mp hx)
    rcases he with he | he
    · have hh := D.side_ax
      rw [he, dist_self] at hh
      norm_num at hh
    · have hh := D.diagonal_bx
      rw [he, dist_self] at hh
      nlinarith
  · intro hyG
    have he := (D.polygon_neighbors D.y).mp
      ((edge_face_iff (uniform_finitePolytope hA.1) hG hvG hyG).mp hy)
    rcases he with he | he
    · have hh := D.diagonal_ay
      rw [he, dist_self] at hh
      nlinarith
    · have hh := D.side_by
      rw [he, dist_self] at hh
      norm_num at hh

end Uniform5.Composition
