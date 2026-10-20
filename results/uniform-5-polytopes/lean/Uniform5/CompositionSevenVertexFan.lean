import Uniform5.CompositionSevenVertexObstruction

/-! The genuine fan-edge coverage implication for the seven-point
obstruction, separating local facet edge calculations from global incidence. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finitePolytope_seven_vertex_fan_impossible {V : Set E}
    (hV : FinitePolytope V) (hd : affineDimension V = 4)
    (p : Fin 7 → E) (hp : Function.Injective p)
    (hvertices : Set.range p = V.extremePoints ℝ)
    (F : Fin 4 → Set E) (hF : ∀ k, IsConvexFace V (F k))
    (hcover : ∀ i j, Edge V (p i) (p j) → ∃ k, p i ∈ F k ∧ p j ∈ F k)
    (hlists : ∀ k i j, Edge (F k) (p i) (p j) ↔ j ∈ CaseB.s1iiiFacetNeighbours k i) :
    False := by
  apply finitePolytope_seven_vertex_graph_impossible hV hd p hp hvertices
  intro i j
  have htable : j ∈ CaseB.s1iiiNeighbours i ↔
      ∃ k : Fin 4, j ∈ CaseB.s1iiiFacetNeighbours k i := by
    rw [← CaseB.s1iii_facet_lists_union]
    simp
  rw [htable]
  constructor
  · intro he
    obtain ⟨k, hi, hj⟩ := hcover i j he
    exact ⟨k, (hlists k i j).mp ((edge_face_iff hV (hF k) hi hj).mp he)⟩
  · rintro ⟨k, hk⟩
    have he := (hlists k i j).mpr hk
    exact (edge_face_iff hV (hF k) he.1.1 he.2.1.1).mpr he

end Uniform5.Composition
