import Uniform5.CompositionAntiprismPyramidEdges
import Uniform5.CompositionThreeFaceUniqueness

/-! A genuine different three-cell at the polygon has the apex neighbor
of the square-pyramid chart; this is forced by actual face incidence. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AntiprismPrismNeighborChart.cell_lateral_eq_apex
    {P K C H G : Set E} {v z : E} {n : ℕ}
    (D : AntiprismPrismNeighborChart K C G v n)
    (hK : FinitePolytope K) (hHK : IsConvexFace K H)
    (hG : IsConvexFace P G) (hC : IsConvexFace P C) (hH : IsConvexFace P H)
    (hGC : G ⊆ C) (hGH : G ⊆ H)
    (hdG : affineDimension G = 2) (hdC : affineDimension C = 3)
    (hdH : affineDimension H = 3) (hne : H ≠ C)
    (hz : Edge H v z) (hzG : z ∉ G) : z = D.apex := by
  have haG := ((D.base.polygon_neighbors D.base.a).mpr (Or.inl rfl)).2.1.1
  have hbG := ((D.base.polygon_neighbors D.base.b).mpr (Or.inr rfl)).2.1.1
  have hzK := (edge_face_iff hK hHK hz.1.1 hz.2.1.1).mpr hz
  have hneG : G.Nonempty := ⟨D.base.a, haG⟩
  rcases (D.neighbors z).mp hzK with he | he | he | he | he
  · exact (hzG (he.symm ▸ haG)).elim
  · exact (hzG (he.symm ▸ hbG)).elim
  · have hxC := ((D.base.neighbors D.base.x).mpr (Or.inr (Or.inr (Or.inl rfl)))).2.1.1
    exact (hne (three_faces_eq_of_common_point hG hH hC hneG hGH hGC
      hdG hdH hdC hz.2.1.1 (he.symm ▸ hxC) hzG)).elim
  · have hyC := ((D.base.neighbors D.base.y).mpr (Or.inr (Or.inr (Or.inr rfl)))).2.1.1
    exact (hne (three_faces_eq_of_common_point hG hH hC hneG hGH hGC
      hdG hdH hdC hz.2.1.1 (he.symm ▸ hyC) hzG)).elim
  · exact he

end Uniform5.Composition
