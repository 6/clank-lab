import Uniform5.CompositionActualAntiprismPrismChart
import Uniform5.CompositionCaseBCellSeparation

/-! The actual F3 pyramid can use a previously selected antiprism cell. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual antiprism cell containing a selected large polygon is unique. -/
theorem antiprismPrism_antiprism_cell_unique {K G C D : Set E} {n : ℕ}
    (hK : UnitUniform 4 K) (hn : 5 ≤ n) (hmodel : Congruent K (antiprismPrismModel n))
    (hG : PolygonFace K G n) (hC : Facet K C) (hD : Facet K D)
    (hGC : G ⊆ C) (hGD : G ⊆ D)
    (hCA : Congruent C (antiprismModel n)) (hDA : Congruent D (antiprismModel n)) : C = D := by
  by_contra hne
  rcases unitUniform4_antiprismPrism_word_cells (by omega : 3 ≤ n) (by omega : n ≠ 4)
    hK hG hC hD hGC hGD hne hmodel with h | h
  · exact unitUniform3_prism_antiprism_disjoint (by omega) (unitUniform_facet hK hD) h.2 hDA
  · exact unitUniform3_prism_antiprism_disjoint (by omega) (unitUniform_facet hK hC) h.1 hCA

/-- Full actual F3 chart with an already specified antiprism cell. -/
theorem unitUniform4_antiprismPrism_specified_chart {K G C : Set E} {v : E} {n : ℕ}
    (hK : UnitUniform 4 K) (hn : 5 ≤ n) (hmodel : Congruent K (antiprismPrismModel n))
    (hG : PolygonFace K G n) (hv : v ∈ G.extremePoints ℝ)
    (hC : Facet K C) (hGC : G ⊆ C) (hCA : Congruent C (antiprismModel n)) :
    Nonempty (AntiprismPrismNeighborChart K C G v n) := by
  obtain ⟨_, D, hD, hGD, hDA, T⟩ := unitUniform4_antiprismPrism_neighbor_chart hK
    (by omega : 3 ≤ n) hn hmodel hG hv
  have he := antiprismPrism_antiprism_cell_unique hK hn hmodel hG hD hC hGD hGC hDA hCA
  rwa [he] at T

/-- Two incident antiprism-prism facets may use literally the same base
chart; no matching of independent choices is left as a premise. -/
theorem unitUniform4_antiprismPrism_shared_base {K G C : Set E} {v : E} {n : ℕ}
    (hK : UnitUniform 4 K) (hn : 5 ≤ n) (hmodel : Congruent K (antiprismPrismModel n))
    (hG : PolygonFace K G n) (hv : v ∈ G.extremePoints ℝ)
    (hC : Facet K C) (hGC : G ⊆ C) (hCA : Congruent C (antiprismModel n))
    (B : AntiprismNeighborChart C G v n) :
    ∃ D : AntiprismPrismNeighborChart K C G v n, D.base = B := by
  obtain ⟨D⟩ := unitUniform4_antiprismPrism_specified_chart hK hn hmodel hG hv hC hGC hCA
  exact ⟨D.rebase B, rfl⟩

/-- The pyramid chart describes the entire actual facet of the parent
vertex figure, and that hull has dimension three. -/
theorem unitUniform5_antiprismPrism_facet_figure {P K G : Set (Space 5)} {v : Space 5} {n : ℕ}
    (hP : UnitUniform 5 P) (hK : Facet P K) (hn : 5 ≤ n)
    (hmodel : Congruent K (antiprismPrismModel n)) (hG : PolygonFace K G n)
    (hv : v ∈ G.extremePoints ℝ) :
    ∃ C, Facet K C ∧ G ⊆ C ∧ Congruent C (antiprismModel n) ∧
      ∃ D : AntiprismPrismNeighborChart K C G v n,
        K ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) =
          convexHull ℝ ({D.base.a, D.base.b, D.base.x, D.base.y, D.apex} : Set (Space 5)) ∧
        affineDimension (convexHull ℝ
          ({D.base.a, D.base.b, D.base.x, D.base.y, D.apex} : Set (Space 5))) = 3 := by
  have hKU := unitUniform_facet hP hK
  obtain ⟨_, C, hC, hGC, hCA, D⟩ := unitUniform4_antiprismPrism_neighbor_chart hKU
    (by omega : 3 ≤ n) hn hmodel hG hv
  obtain ⟨D⟩ := D
  have hvK := hG.1.2.extremePoints_subset_extremePoints hv
  have he : K ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) =
      convexHull ℝ ({D.base.a, D.base.b, D.base.x, D.base.y, D.apex} : Set (Space 5)) := by
    rw [uniform_vertexFigure_face_inter hP.1 hK.1 hK.2.1 (hG.1.2.1 hv.1)]
    exact D.figure_eq hKU hvK
  refine ⟨C, hC, hGC, hCA, D, he, ?_⟩
  have hd := (unitUniform5_facet_figure_placement hP hK hvK).2.2.2.1
  rwa [he] at hd

end Uniform5.Composition
