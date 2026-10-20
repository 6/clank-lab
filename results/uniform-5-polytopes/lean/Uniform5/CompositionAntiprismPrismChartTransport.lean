import Uniform5.CompositionAntiprismPrismChart

/-! Isometric transport of the complete five-neighbor F3 chart. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def AntiprismPrismNeighborChart.map {K C G : Set E} {v : E} {n : ℕ}
    (D : AntiprismPrismNeighborChart K C G v n) (f : E →ᵃⁱ[ℝ] F) :
    AntiprismPrismNeighborChart (f '' K) (f '' C) (f '' G) (f v) n where
  base := D.base.map f
  apex := f D.apex
  neighbors := by
    intro z
    constructor
    · intro he
      obtain ⟨x, hx, rfl⟩ := he.2.1.1
      have hh := (D.neighbors x).mp (embedding_edge_reflect f he)
      rcases hh with h | h | h | h | h
      · exact Or.inl (congrArg f h)
      · exact Or.inr (Or.inl (congrArg f h))
      · exact Or.inr (Or.inr (Or.inl (congrArg f h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg f h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (congrArg f h))))
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact embedding_edge_image f ((D.neighbors _).mpr (Or.inl rfl))
      · exact embedding_edge_image f ((D.neighbors _).mpr (Or.inr (Or.inl rfl)))
      · exact embedding_edge_image f ((D.neighbors _).mpr (Or.inr (Or.inr (Or.inl rfl))))
      · exact embedding_edge_image f ((D.neighbors _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact embedding_edge_image f ((D.neighbors _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  apex_a := (f.dist_map _ _).trans D.apex_a
  apex_b := (f.dist_map _ _).trans D.apex_b
  apex_x := (f.dist_map _ _).trans D.apex_x
  apex_y := (f.dist_map _ _).trans D.apex_y

/-- Any chart of the same actual antiprism cell can be used as the base.
Exhaustive actual incidence resolves all possible label alignments. -/
noncomputable def AntiprismPrismNeighborChart.rebase {K C G : Set E} {v : E} {n : ℕ}
    (D : AntiprismPrismNeighborChart K C G v n) (B : AntiprismNeighborChart C G v n) :
    AntiprismPrismNeighborChart K C G v n where
  base := B
  apex := D.apex
  neighbors := by
    intro z
    have he := (D.base.neighbors z).symm.trans (B.neighbors z)
    rw [D.neighbors]
    tauto
  apex_a := by
    have he := (D.base.neighbors B.a).mp ((B.neighbors _).mpr (Or.inl rfl))
    rcases he with he | he | he | he <;> rw [he]
    · exact D.apex_a
    · exact D.apex_b
    · exact D.apex_x
    · exact D.apex_y
  apex_b := by
    have he := (D.base.neighbors B.b).mp ((B.neighbors _).mpr (Or.inr (Or.inl rfl)))
    rcases he with he | he | he | he <;> rw [he]
    · exact D.apex_a
    · exact D.apex_b
    · exact D.apex_x
    · exact D.apex_y
  apex_x := by
    have he := (D.base.neighbors B.x).mp ((B.neighbors _).mpr (Or.inr (Or.inr (Or.inl rfl))))
    rcases he with he | he | he | he <;> rw [he]
    · exact D.apex_a
    · exact D.apex_b
    · exact D.apex_x
    · exact D.apex_y
  apex_y := by
    have he := (D.base.neighbors B.y).mp ((B.neighbors _).mpr (Or.inr (Or.inr (Or.inr rfl))))
    rcases he with he | he | he | he <;> rw [he]
    · exact D.apex_a
    · exact D.apex_b
    · exact D.apex_x
    · exact D.apex_y

end Uniform5.Composition
