import Uniform5.CompositionChartEdges
import Uniform5.CompositionDuoprismChart
import Uniform5.CompositionFigureRidgeCorrespondence

/-! A genuine four-neighbor figure is a tetrahedron by dimension and incidence. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem unitUniform4_four_neighbor_figure_edges {K : Set E} {v a b c d : E}
    (hK : UnitUniform 4 K)
    (hneighbors : ∀ z, Edge K v z ↔ z = a ∨ z = b ∨ z = c ∨ z = d) :
    let Q := vertexFigure K v (vertexCentroid (vertices K (uniform_finitePolytope hK.1)))
    ∀ x y, Edge Q x y ↔
      (x = a ∨ x = b ∨ x = c ∨ x = d) ∧
      (y = a ∨ y = b ∨ y = c ∨ y = d) ∧ x ≠ y := by
  let hKP := uniform_finitePolytope hK.1
  let center := vertexCentroid (vertices K hKP)
  let Q := vertexFigure K v center
  have hv : v ∈ K.extremePoints ℝ := ((hneighbors _).mpr (Or.inl rfl)).1
  obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical hKP (uniform_vertexTransitive hK.1)
  have hQ : FinitePolytope Q := finitePolytope_vertexFigure_of_positiveDimension
    hKP hv center R hs hK.2 (by rw [uniform_dimension hK.1]; norm_num)
  have hQK : Q ⊆ K := fun _ hx => hx.1
  have hself : K ∩ Q = Q := Set.inter_eq_right.mpr hQK
  have hdQ : affineDimension Q = 3 := by
    have hh := (unitUniform_vertexFigure_face_correspondence (n := 1) hK hv 3).1 K
      (finitePolytope_self_face hKP) hv.1 (by simpa using uniform_dimension hK.1)
    have hh' : affineDimension (K ∩ Q) = 3 := hh.2.2
    rwa [hself] at hh'
  have hext : Q.extremePoints ℝ = {a, b, c, d} := by
    rw [show Q = vertexFigure K v center from rfl,
      finitePolytope_unit_vertexFigure_extremePoints hKP hv center R hs hK.2]
    ext z
    exact hneighbors z
  dsimp only
  intro x y
  constructor
  · intro he
    refine ⟨?_, ?_, he.2.2.1⟩
    · have hh : x ∈ Q.extremePoints ℝ := he.1
      simpa only [hext, mem_insert_iff, mem_singleton_iff] using hh
    · have hh : y ∈ Q.extremePoints ℝ := he.2.1
      simpa only [hext, mem_insert_iff, mem_singleton_iff] using hh
  · rintro ⟨hx, hy, hne⟩
    exact (tetrahedron_complete_graph hQ hdQ hext (hext.symm ▸ hx) (hext.symm ▸ hy)).mpr hne

end Uniform5.Composition
