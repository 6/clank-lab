import Uniform5.CompositionAntiprismPyramidEdges

/-! A full relational edge formula, including exclusion of points outside
the actual five-vertex pyramid, for finite fan labeling. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AntiprismPrismNeighborChart.figure_edges {K C G : Set E} {v : E} {n : ℕ}
    (D : AntiprismPrismNeighborChart K C G v n) (hK : UnitUniform 4 K)
    (hC : Facet K C) (hn : 3 ≤ n) :
    let Q := vertexFigure K v (vertexCentroid (vertices K (uniform_finitePolytope hK.1)))
    ∀ u w, Edge Q u w ↔
      (u = D.base.a ∧ (w = D.base.b ∨ w = D.base.x ∨ w = D.apex)) ∨
      (u = D.base.b ∧ (w = D.base.a ∨ w = D.base.y ∨ w = D.apex)) ∨
      (u = D.base.x ∧ (w = D.base.a ∨ w = D.base.y ∨ w = D.apex)) ∨
      (u = D.base.y ∧ (w = D.base.b ∨ w = D.base.x ∨ w = D.apex)) ∨
      (u = D.apex ∧ (w = D.base.a ∨ w = D.base.b ∨ w = D.base.x ∨ w = D.base.y)) := by
  dsimp only
  obtain ⟨ha, hb, hx, hy, hz⟩ := D.figure_neighbors hK hC hn
  have hv := ((D.neighbors D.base.a).mpr (Or.inl rfl)).1
  intro u w
  constructor
  · intro he
    have hu : u ∈ ({D.base.a, D.base.b, D.base.x, D.base.y, D.apex} : Set E) := by
      have hh := he.1
      rw [D.figure_eq hK hv] at hh
      exact extremePoints_convexHull_subset hh
    simp only [mem_insert_iff, mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨rfl, (ha w).mp he⟩
    · exact Or.inr (Or.inl ⟨rfl, (hb w).mp he⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, (hx w).mp he⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (hy w).mp he⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, (hz w).mp he⟩)))
  · rintro (⟨rfl, hh⟩ | ⟨rfl, hh⟩ | ⟨rfl, hh⟩ | ⟨rfl, hh⟩ | ⟨rfl, hh⟩)
    · exact (ha w).mpr hh
    · exact (hb w).mpr hh
    · exact (hx w).mpr hh
    · exact (hy w).mpr hh
    · exact (hz w).mpr hh

end Uniform5.Composition
