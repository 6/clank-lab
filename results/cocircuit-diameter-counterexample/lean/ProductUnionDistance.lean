import FactorUnionDistance

namespace ADKZPricing
open Matrix Finset
noncomputable section

theorem leftStar_natAdd {n m : ℕ} (e : Fin m) :
    leftStar (some (Fin.natAdd n e)) = none := by
  change (Fin.addCases (m := n) (n := m) (motive := fun _ => Fin n ⊕ Fin m)
    Sum.inl Sum.inr (Fin.natAdd n e)).getLeft? = none
  rw [Fin.addCases_right]
  rfl

theorem rightStar_natAdd {n m : ℕ} (e : Fin m) :
    rightStar (some (Fin.natAdd n e)) = some e := by
  change (Fin.addCases (m := n) (n := m) (motive := fun _ => Fin n ⊕ Fin m)
    Sum.inl Sum.inr (Fin.natAdd n e)).getRight? = some e
  rw [Fin.addCases_right]
  rfl

theorem product_uniform_vertex {n m d e : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℝ) (B : Matrix (Fin m) (Fin (e + 1)) ℝ)
    (huA : RowUniform A) (huB : RowUniform B)
    (c : Option (Fin (n + m))) (Z : Finset (Fin n)) (W : Finset (Fin m)) :
    (productChartCell A B c).vertex (Z, W) ↔
      (LabelledCell.cartesian (chartCell A (leftStar c)) (chartCell B (rightStar c))).vertex (Z, W) :=
  product_chart_vertex_iff A B huA huB c Z W

theorem product_uniform_edge {n m d e : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℝ) (B : Matrix (Fin m) (Fin (e + 1)) ℝ)
    (huA : RowUniform A) (huB : RowUniform B)
    (c : Option (Fin (n + m))) (Z W : Finset (Fin n) × Finset (Fin m)) :
    (productChartCell A B c).edge Z W ↔
      (LabelledCell.cartesian (chartCell A (leftStar c)) (chartCell B (rightStar c))).edge Z W :=
  product_chart_edge_iff A B huA huB c Z W

/-- The actual product-star two-cell union has designated distance≥42
    once its actual factor's central designated distance≥21 is supplied.
    The exceptional row is fixed and lies in exactly one factor; the
    other factor's central membership guards are retained on every step. -/
theorem product_star_union_distance (A : Matrix (Fin 40) (Fin 21) ℝ)
    (hu : RowUniform A) (Z W : Finset (Fin 40))
    (hz : ChartVertex A none Z) (hw : ChartVertex A none W)
    (hcomp : ∀ i, i ∈ Z ↔ i ∉ W)
    (hcentral : ∀ k, LabelledCell.CellWalk (chartCell A none) Z W k → 21 ≤ k)
    (e : Fin 80) {L : ℕ}
    (h : LabelledCell.CellWalk (LabelledCell.union (productChartCell A A none)
      (productChartCell A A (some e))) (Z, Z) (W, W) L) : 42 ≤ L := by
  revert h
  refine Fin.addCases (m := 40) (n := 40)
    (motive := fun e => LabelledCell.CellWalk
      (LabelledCell.union (productChartCell A A none)
        (productChartCell A A (some e))) (Z, Z) (W, W) L → 42 ≤ L)
    (fun e => ?_) (fun e => ?_) e
  · intro h
    have hp : LabelledCell.CellWalk (LabelledCell.union
        (LabelledCell.cartesian (chartCell A none) (chartCell A none))
        (LabelledCell.cartesian (chartCell A (some e)) (chartCell A none))) (Z, Z) (W, W) L := by
      apply h.transfer
      · intro z hv
        rcases hv with hv | hv
        · exact Or.inl ((product_uniform_vertex A A hu hu none z.1 z.2).mp hv)
        · have he := (product_uniform_vertex A A hu hu (some (Fin.castAdd 40 e)) z.1 z.2).mp hv
          exact Or.inr (by simpa [leftStar, rightStar, finSumFinEquiv] using he)
      · intro z w he
        rcases he with he | he
        · exact Or.inl ((product_uniform_edge A A hu hu none z w).mp he)
        · have ht := (product_uniform_edge A A hu hu (some (Fin.castAdd 40 e)) z w).mp he
          exact Or.inr (by simpa [leftStar, rightStar, finSumFinEquiv] using ht)
    exact LabelledCell.left_union_walk_lower_bound (chartCell A none) (chartCell A (some e))
      (chartCell A none) (Z, Z) (W, W) 21 21
      (fun _ p => factor_cell_union_lower_bound A hu Z W hz hw hcomp hcentral e p) hcentral hp
  · intro h
    have hp : LabelledCell.CellWalk (LabelledCell.union
        (LabelledCell.cartesian (chartCell A none) (chartCell A none))
        (LabelledCell.cartesian (chartCell A none) (chartCell A (some e)))) (Z, Z) (W, W) L := by
      apply h.transfer
      · intro z hv
        rcases hv with hv | hv
        · exact Or.inl ((product_uniform_vertex A A hu hu none z.1 z.2).mp hv)
        · have he := (product_uniform_vertex A A hu hu (some (Fin.natAdd 40 e)) z.1 z.2).mp hv
          exact Or.inr (by simpa only [leftStar_natAdd, rightStar_natAdd] using he)
      · intro z w he
        rcases he with he | he
        · exact Or.inl ((product_uniform_edge A A hu hu none z w).mp he)
        · have ht := (product_uniform_edge A A hu hu (some (Fin.natAdd 40 e)) z w).mp he
          exact Or.inr (by simpa only [leftStar_natAdd, rightStar_natAdd] using ht)
    exact LabelledCell.right_union_walk_lower_bound (chartCell A none) (chartCell A none)
      (chartCell A (some e)) (Z, Z) (W, W) 21 21 hcentral
      (fun _ p => factor_cell_union_lower_bound A hu Z W hz hw hcomp hcentral e p) hp

#print axioms product_star_union_distance
end
end ADKZPricing
