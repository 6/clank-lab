import Uniform5.CompositionAntiprismChart

/-! One isometric embedding transports the whole antiprism chart. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The chart's edge incidences, exhaustive neighbor list and metric use
one and the same isometric embedding. -/
noncomputable def AntiprismNeighborChart.map {K G : Set E} {v : E} {n : ℕ}
    (D : AntiprismNeighborChart K G v n) (f : E →ᵃⁱ[ℝ] F) :
    AntiprismNeighborChart (f '' K) (f '' G) (f v) n where
  a := f D.a
  b := f D.b
  x := f D.x
  y := f D.y
  neighbors := by
    intro z
    constructor
    · intro he
      obtain ⟨x, hx, rfl⟩ := he.2.1.1
      have hh := (D.neighbors x).mp (embedding_edge_reflect f he)
      rcases hh with h | h | h | h
      · exact Or.inl (congrArg f h)
      · exact Or.inr (Or.inl (congrArg f h))
      · exact Or.inr (Or.inr (Or.inl (congrArg f h)))
      · exact Or.inr (Or.inr (Or.inr (congrArg f h)))
    · rintro (rfl | rfl | rfl | rfl)
      · exact embedding_edge_image f ((D.neighbors D.a).mpr (Or.inl rfl))
      · exact embedding_edge_image f ((D.neighbors D.b).mpr (Or.inr (Or.inl rfl)))
      · exact embedding_edge_image f ((D.neighbors D.x).mpr (Or.inr (Or.inr (Or.inl rfl))))
      · exact embedding_edge_image f ((D.neighbors D.y).mpr (Or.inr (Or.inr (Or.inr rfl))))
  polygon_neighbors := by
    intro z
    constructor
    · intro he
      obtain ⟨x, hx, rfl⟩ := he.2.1.1
      have hh := (D.polygon_neighbors x).mp (embedding_edge_reflect f he)
      exact hh.elim (fun h => Or.inl (congrArg f h)) (fun h => Or.inr (congrArg f h))
    · rintro (rfl | rfl)
      · exact embedding_edge_image f ((D.polygon_neighbors D.a).mpr (Or.inl rfl))
      · exact embedding_edge_image f ((D.polygon_neighbors D.b).mpr (Or.inr rfl))
  chord_ab := (f.dist_map _ _).trans D.chord_ab
  side_xy := (f.dist_map _ _).trans D.side_xy
  side_ax := (f.dist_map _ _).trans D.side_ax
  side_by := (f.dist_map _ _).trans D.side_by
  diagonal_ay := by rw [f.dist_map]; exact D.diagonal_ay
  diagonal_bx := by rw [f.dist_map]; exact D.diagonal_bx

end Uniform5.Composition
