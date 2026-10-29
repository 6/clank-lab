import ChartVertexTransport
import CellWalkSequence

namespace ADKZPricing
open Matrix Finset
noncomputable section

def productLabelPair {n m : ℕ} (Z : Finset (Fin (n + m))) : Finset (Fin n) × Finset (Fin m) :=
  (leftLabels Z, rightLabels Z)

/-- Both field maps and the original row concatenation commute in the
    actual construction; every original product label is retained. -/
theorem second_chart_vertex_pair {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n) (c : Option (Fin (n + n)))
    (Z : Finset (Fin (n + n))) :
    ChartVertex ((secondPerturbedMatrix A C h0).map (Rat.castHom ℝ)) c Z ↔
      (productChartCell ((chartedGenericFactor A C).map (Rat.castHom ℝ))
        ((chartedGenericFactor A C).map (Rat.castHom ℝ)) c).vertex (productLabelPair Z) := by
  change _ ↔ ChartVertex _ c (productLabels (leftLabels Z) (rightLabels Z))
  rw [productLabels_split]
  simpa only [firstProduct, orderedProduct_map] using second_real_chart_vertices A C h0 hn c Z

/-- This is exact edge transport, with actual endpoint membership guards
    and the same complete shared-row set, through the second perturbation. -/
theorem second_chart_edge_pair {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n) (c : Option (Fin (n + n)))
    (Z W : Finset (Fin (n + n))) :
    (chartCell ((secondPerturbedMatrix A C h0).map (Rat.castHom ℝ)) c).edge Z W ↔
      (productChartCell ((chartedGenericFactor A C).map (Rat.castHom ℝ))
        ((chartedGenericFactor A C).map (Rat.castHom ℝ)) c).edge (productLabelPair Z) (productLabelPair W) := by
  change (ChartVertex _ c Z ∧ ChartVertex _ c W ∧ _) ↔
    (ChartVertex _ c (productLabels (leftLabels Z) (rightLabels Z)) ∧
      ChartVertex _ c (productLabels (leftLabels W) (rightLabels W)) ∧ _)
  rw [productLabels_split, productLabels_split]
  have hZ := second_real_chart_vertices A C h0 hn c Z
  have hW := second_real_chart_vertices A C h0 hn c W
  simp only [firstProduct, orderedProduct_map] at hZ hW
  exact and_congr hZ (and_congr hW (by simp only [productLabelPair, productLabels_split]))

/-- Literal two-cell union transport uses ONE label-pair map on the
    entire path. Shared-facet vertices and edges remain in both cells. -/
theorem second_union_pair_walk {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n) (c c' : Option (Fin (n + n)))
    {Z W : Finset (Fin (n + n))} {L : ℕ}
    (h : LabelledCell.CellWalk (LabelledCell.union
      (chartCell ((secondPerturbedMatrix A C h0).map (Rat.castHom ℝ)) c)
      (chartCell ((secondPerturbedMatrix A C h0).map (Rat.castHom ℝ)) c')) Z W L) :
    let F := (chartedGenericFactor A C).map (Rat.castHom ℝ)
    LabelledCell.CellWalk (LabelledCell.union (productChartCell F F c) (productChartCell F F c'))
      (productLabelPair Z) (productLabelPair W) L := by
  apply h.map productLabelPair
  · intro Z hz
    rcases hz with hz | hz
    · exact Or.inl ((second_chart_vertex_pair A C h0 hn c Z).mp hz)
    · exact Or.inr ((second_chart_vertex_pair A C h0 hn c' Z).mp hz)
  · intro Z W he
    rcases he with he | he
    · exact Or.inl ((second_chart_edge_pair A C h0 hn c Z W).mp he)
    · exact Or.inr ((second_chart_edge_pair A C h0 hn c' Z W).mp he)

#print axioms second_chart_edge_pair
#print axioms second_union_pair_walk
end
end ADKZPricing
