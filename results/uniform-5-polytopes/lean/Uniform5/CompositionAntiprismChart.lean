import Uniform5.CompositionAntiprismTrapezoidMetric
import Uniform5.CompositionTwoLayerFaces
import Uniform5.CompositionFacetFigures

/-! Exhaustive intrinsic antiprism vertex-figure charts. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The four actual neighbors form the F3 cyclic trapezoid in order a,b,y,x.
The distinguished polygon has exactly the two neighbors a,b. -/
structure AntiprismNeighborChart (A G : Set E) (v : E) (n : ℕ) where
  a : E
  b : E
  x : E
  y : E
  neighbors : ∀ z, Edge A v z ↔ z = a ∨ z = b ∨ z = x ∨ z = y
  polygon_neighbors : ∀ z, Edge G v z ↔ z = a ∨ z = b
  chord_ab : dist a b = CaseB.chord n
  side_xy : dist x y = 1
  side_ax : dist a x = 1
  side_by : dist b y = 1
  diagonal_ay : dist a y ^ 2 = 1 + CaseB.chord n
  diagonal_bx : dist b x ^ 2 = 1 + CaseB.chord n

/-- The chart exhausts the entire intrinsic vertex figure. -/
theorem AntiprismNeighborChart.figure_eq [FiniteDimensional ℝ E]
    {A G : Set E} {v : E} {n : ℕ} (D : AntiprismNeighborChart A G v n)
    (hA : UnitUniform 3 A) (hv : v ∈ A.extremePoints ℝ) :
    vertexFigure A v (vertexCentroid (vertices A (uniform_finitePolytope hA.1))) =
      convexHull ℝ ({D.a, D.b, D.x, D.y} : Set E) := by
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hA.1
  rw [finitePolytope_unit_vertexFigure (uniform_finitePolytope hA.1) hv _ (intrinsicRadius A) hs hA.2]
  congr 1
  ext z
  exact D.neighbors z

/-- Concrete chart at the upper vertex with index one. -/
theorem antiprism_one_chart {n : ℕ} (hn : 3 ≤ n) (hA : UnitUniform 3 (antiprismModel n)) :
    Nonempty (AntiprismNeighborChart (antiprismModel n) (antiprismLayer n false)
      (antiprismPoint n false ⟨1, by omega⟩) n) := by
  obtain ⟨hab, hxy, hax, hby, hay, hbx⟩ := antiprism_one_trapezoid_metric hn
  refine ⟨{
    a := antiprismPoint n false ⟨0, by omega⟩,
    b := antiprismPoint n false ⟨2, by omega⟩,
    x := antiprismPoint n true ⟨0, by omega⟩,
    y := antiprismPoint n true ⟨1, by omega⟩,
    neighbors := antiprism_one_neighbors hn hA,
    polygon_neighbors := ?_, chord_ab := hab, side_xy := hxy,
    side_ax := hax, side_by := hby, diagonal_ay := hay, diagonal_bx := hbx }⟩
  intro z
  rw [antiprismLayer_eq_image]
  constructor
  · intro he
    obtain ⟨z', hz', rfl⟩ := he.2.1.1
    rw [← antiprismLayerSlice_point n false] at he
    have hh := (unitPolygon_one_neighbors hn z').mp
      (embedding_edge_reflect (antiprismLayerSlice n false) he)
    rcases hh with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · simpa only [antiprismLayerSlice_point] using embedding_edge_image (antiprismLayerSlice n false)
        ((unitPolygon_one_neighbors hn _).mpr (Or.inl rfl))
    · simpa only [antiprismLayerSlice_point] using embedding_edge_image (antiprismLayerSlice n false)
        ((unitPolygon_one_neighbors hn _).mpr (Or.inr rfl))

end Uniform5.Composition
