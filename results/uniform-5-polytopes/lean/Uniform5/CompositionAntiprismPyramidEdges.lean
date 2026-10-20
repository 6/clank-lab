import Uniform5.CompositionAntiprismChartEdges
import Uniform5.CompositionAntiprismPrismSpecifiedCell

/-! Exact edge lists of the actual square-pyramid figure facets. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AntiprismPrismNeighborChart.figure_neighbors {K C G : Set E} {v : E} {n : ℕ}
    (D : AntiprismPrismNeighborChart K C G v n) (hK : UnitUniform 4 K)
    (hC : Facet K C) (hn : 3 ≤ n) :
    let Q := vertexFigure K v (vertexCentroid (vertices K (uniform_finitePolytope hK.1)))
    (∀ z, Edge Q D.base.a z ↔ z = D.base.b ∨ z = D.base.x ∨ z = D.apex) ∧
    (∀ z, Edge Q D.base.b z ↔ z = D.base.a ∨ z = D.base.y ∨ z = D.apex) ∧
    (∀ z, Edge Q D.base.x z ↔ z = D.base.a ∨ z = D.base.y ∨ z = D.apex) ∧
    (∀ z, Edge Q D.base.y z ↔ z = D.base.b ∨ z = D.base.x ∨ z = D.apex) ∧
    (∀ z, Edge Q D.apex z ↔ z = D.base.a ∨ z = D.base.b ∨ z = D.base.x ∨ z = D.base.y) := by
  let hKP := uniform_finitePolytope hK.1
  let c := vertexCentroid (vertices K hKP)
  let Q := vertexFigure K v c
  have hCU : UnitUniform 3 C := unitUniform_facet hK hC
  let B := vertexFigure C v (vertexCentroid (vertices C (uniform_finitePolytope hCU.1)))
  have hvC : v ∈ C.extremePoints ℝ := ((D.base.neighbors _).mpr (Or.inl rfl)).1
  have hvK : v ∈ K.extremePoints ℝ := hC.1.2.extremePoints_subset_extremePoints hvC
  obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical hKP (uniform_vertexTransitive hK.1)
  have hQ : FinitePolytope Q := finitePolytope_vertexFigure_of_positiveDimension
    hKP hvK c R hs hK.2 (by rw [uniform_dimension hK.1]; norm_num)
  have hQK : Q ⊆ K := fun _ hx => hx.1
  have hself : K ∩ Q = Q := Set.inter_eq_right.mpr hQK
  have hdQ : affineDimension Q = 3 := by
    have hh := (unitUniform_vertexFigure_face_correspondence (n := 1) hK hvK 3).1 K
      (finitePolytope_self_face hKP) hvK.1 (by simpa using uniform_dimension hK.1)
    have hh' : affineDimension (K ∩ Q) = 3 := hh.2.2
    rwa [hself] at hh'
  have hCB : C ∩ Q = B := uniform_vertexFigure_face_inter hK.1 hC.1 hC.2.1 hvC.1
  have hB : IsConvexFace Q B := by
    rw [← hCB]
    exact ((unitUniform_vertexFigure_facet_correspondence (n := 1) hK hvK).1 C hC hvC.1).1
  obtain ⟨_, _, hsC⟩ := uniform_hasIntrinsicRadius hCU.1
  have heB : B.extremePoints ℝ = {D.base.a, D.base.b, D.base.x, D.base.y} := by
    rw [show B = vertexFigure C v _ from rfl,
      finitePolytope_unit_vertexFigure_extremePoints (uniform_finitePolytope hCU.1) hvC _ (intrinsicRadius C) hsC hCU.2]
    ext z
    exact D.base.neighbors z
  have heQ : Q.extremePoints ℝ = {D.base.a, D.base.b, D.base.x, D.base.y, D.apex} := by
    rw [show Q = vertexFigure K v c from rfl,
      finitePolytope_unit_vertexFigure_extremePoints hKP hvK c R hs hK.2]
    ext z
    exact D.neighbors z
  have hcover : ∀ w ∈ Q.extremePoints ℝ, w ∈ B ∨ w = D.apex := by
    intro w hw
    rw [heQ] at hw
    simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ((show D.base.a ∈ B.extremePoints ℝ by rw [heB]; simp).1)
    · exact Or.inl ((show D.base.b ∈ B.extremePoints ℝ by rw [heB]; simp).1)
    · exact Or.inl ((show D.base.x ∈ B.extremePoints ℝ by rw [heB]; simp).1)
    · exact Or.inl ((show D.base.y ∈ B.extremePoints ℝ by rw [heB]; simp).1)
    · exact Or.inr rfl
  obtain ⟨ha, hb, hx, hy⟩ := D.base.figure_neighbors hCU hn hvC
  have ha' := pyramid_base_vertex_neighbors hQ hdQ hB
    (show D.base.a ∈ B.extremePoints ℝ by rw [heB]; simp) ha hcover
  have hb' := pyramid_base_vertex_neighbors hQ hdQ hB
    (show D.base.b ∈ B.extremePoints ℝ by rw [heB]; simp) hb hcover
  have hx' := pyramid_base_vertex_neighbors hQ hdQ hB
    (show D.base.x ∈ B.extremePoints ℝ by rw [heB]; simp) hx hcover
  have hy' := pyramid_base_vertex_neighbors hQ hdQ hB
    (show D.base.y ∈ B.extremePoints ℝ by rw [heB]; simp) hy hcover
  refine ⟨ha', hb', hx', hy', ?_⟩
  intro z
  constructor
  · intro he
    have hz := he.2.1
    rw [heQ] at hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact (he.2.2.1 h.symm).elim
  · rintro (rfl | rfl | rfl | rfl)
    · exact chart_edge_symm ((ha' _).mpr (Or.inr (Or.inr rfl)))
    · exact chart_edge_symm ((hb' _).mpr (Or.inr (Or.inr rfl)))
    · exact chart_edge_symm ((hx' _).mpr (Or.inr (Or.inr rfl)))
    · exact chart_edge_symm ((hy' _).mpr (Or.inr (Or.inr rfl)))

end Uniform5.Composition
