import Uniform5.CompositionPlanarNeighbors

/-! Diagonal exclusion by planar incidence. A parent edge whose endpoints
lie in a convex subhull is still an edge of that subhull. Once two planar
neighbors are known, there are no additional parent edges within it. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem edge_restrict_convex_subset {P C : Set E} (hC : Convex ℝ C) (hCP : C ⊆ P)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) (he : Edge P x y) : Edge C x y := by
  refine ⟨?_, ?_, he.2.2.1, he.2.2.2.mono hCP (hC.segment_subset hx hy)⟩
  · exact ⟨hx, fun a ha b hb hab => he.1.2 (hCP ha) (hCP hb) hab⟩
  · exact ⟨hy, fun a ha b hb hab => he.2.1.2 (hCP ha) (hCP hb) hab⟩

/-- A planar lateral hull need not itself be a face of the parent. Its
known two cycle edges nevertheless exhaust all parent edges with their
other endpoint in that hull. -/
theorem finitePolytope_planar_subhull_neighbors {P C : Set E}
    (hC : FinitePolytope C) (hd : affineDimension C = 2) (hCP : C ⊆ P)
    {v a b : E} (hv : v ∈ C) (ha : a ∈ C) (hb : b ∈ C)
    (hea : Edge P v a) (heb : Edge P v b) (hab : a ≠ b) :
    ∀ z ∈ C, Edge P v z → z = a ∨ z = b := by
  have hac := edge_restrict_convex_subset (finitePolytope_convex hC) hCP hv ha hea
  have hbc := edge_restrict_convex_subset (finitePolytope_convex hC) hCP hv hb heb
  intro z hz he
  exact (finitePolytope_planar_neighbors hC hd hac hbc hab z).mp
    (edge_restrict_convex_subset (finitePolytope_convex hC) hCP hv hz he)

/-- In particular a nonconsecutive lateral pair cannot be an actual
parent edge; this supplies Wuse's diagonal exclusion without a chosen
intersection coordinate. -/
theorem finitePolytope_planar_subhull_diagonal_not_edge {P C : Set E}
    (hC : FinitePolytope C) (hd : affineDimension C = 2) (hCP : C ⊆ P)
    {v a b z : E} (hv : v ∈ C) (ha : a ∈ C) (hb : b ∈ C) (hz : z ∈ C)
    (hea : Edge P v a) (heb : Edge P v b) (hab : a ≠ b)
    (hza : z ≠ a) (hzb : z ≠ b) : ¬ Edge P v z := by
  intro he
  exact (finitePolytope_planar_subhull_neighbors hC hd hCP hv ha hb hea heb hab z hz he).elim
    hza hzb

end Uniform5.Composition
