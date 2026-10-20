import Uniform5.CompositionChartEdges
import Uniform5.CompositionDuoprismChart
import Uniform5.CompositionFigureRidgeCorrespondence

/-! Every pair of distinct vertices of an actual duoprism figure is an edge. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem DuoprismNeighborChart.figure_edges {K G : Set E} {v : E} {n q : ℕ}
    (D : DuoprismNeighborChart K G v n q) (hK : UnitUniform 4 K) :
    let Q := vertexFigure K v (vertexCentroid (vertices K (uniform_finitePolytope hK.1)))
    ∀ x y, Edge Q x y ↔
      (x = D.a ∨ x = D.b ∨ x = D.g ∨ x = D.d) ∧
      (y = D.a ∨ y = D.b ∨ y = D.g ∨ y = D.d) ∧ x ≠ y := by
  let hKP := uniform_finitePolytope hK.1
  let c := vertexCentroid (vertices K hKP)
  let Q := vertexFigure K v c
  have hv : v ∈ K.extremePoints ℝ := ((D.neighbors _).mpr (Or.inl rfl)).1
  obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical hKP (uniform_vertexTransitive hK.1)
  have hQ : FinitePolytope Q := finitePolytope_vertexFigure_of_positiveDimension
    hKP hv c R hs hK.2 (by rw [uniform_dimension hK.1]; norm_num)
  have hQK : Q ⊆ K := fun _ hx => hx.1
  have hself : K ∩ Q = Q := Set.inter_eq_right.mpr hQK
  have hdQ : affineDimension Q = 3 := by
    have hh := (unitUniform_vertexFigure_face_correspondence (n := 1) hK hv 3).1 K
      (finitePolytope_self_face hKP) hv.1 (by simpa using uniform_dimension hK.1)
    have hh' : affineDimension (K ∩ Q) = 3 := hh.2.2
    rwa [hself] at hh'
  have hext : Q.extremePoints ℝ = {D.a, D.b, D.g, D.d} := by
    rw [show Q = vertexFigure K v c from rfl,
      finitePolytope_unit_vertexFigure_extremePoints hKP hv c R hs hK.2]
    ext z
    exact D.neighbors z
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
