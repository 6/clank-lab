import Uniform5.CompositionAntiprismOneNeighbors

/-! Six exact metric entries of the actual antiprism vertex figure. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- The diagonal increment is the second-neighbor polygon chord. -/
theorem antiprism_diagonal_increment {n : ℕ} (hn : 3 ≤ n) :
    2 * unitPolygonRadius n ^ 2 *
      (Real.cos (Real.pi / n) - Real.cos (3 * (Real.pi / n))) = CaseB.chord n := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hs : Real.sin (Real.pi / n) ≠ 0 := ne_of_gt <|
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (div_lt_self Real.pi_pos hn')
  have hr : 2 * unitPolygonRadius n * Real.sin (Real.pi / n) = 1 := by
    unfold unitPolygonRadius
    field_simp
  rw [Real.cos_three_mul, CaseB.chord]
  have ht := Real.sin_sq_add_cos_sq (Real.pi / n)
  linear_combination 2 * Real.cos (Real.pi / n) * congrArg (fun x : ℝ => x ^ 2) hr -
    8 * unitPolygonRadius n ^ 2 * Real.cos (Real.pi / n) * ht

/-- The four neighbors, in cyclic order upper-zero, upper-two, lower-one,
lower-zero, have the exact F3 trapezoid distances. -/
theorem antiprism_one_trapezoid_metric {n : ℕ} (hn : 3 ≤ n) :
    let a := antiprismPoint n false ⟨0, by omega⟩
    let b := antiprismPoint n false ⟨2, by omega⟩
    let x := antiprismPoint n true ⟨0, by omega⟩
    let y := antiprismPoint n true ⟨1, by omega⟩
    dist a b = CaseB.chord n ∧ dist x y = 1 ∧
      dist a x = 1 ∧ dist b y = 1 ∧
      dist a y ^ 2 = 1 + CaseB.chord n ∧ dist b x ^ 2 = 1 + CaseB.chord n := by
  dsimp only
  refine ⟨?_, ?_, antiprism_cross_same_dist hn _, ?_, ?_, ?_⟩
  · rw [antiprism_same_layer_dist]
    exact unitPolygon_second_dist hn
  · rw [antiprism_same_layer_dist]
    exact unitEdges_unitPolygon hn _ _
      (polygon_first_edge n _ hn (unitPolygonRadius_pos hn))
  · apply (sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp
    rw [antiprism_cross_dist_sq hn]
    norm_num only [Nat.cast_one, Nat.cast_ofNat, mul_one]
    rw [show 2 * Real.pi * 2 / n - (2 * Real.pi / n + Real.pi / n) = Real.pi / n by ring]
    ring
  · rw [antiprism_cross_dist_sq hn]
    norm_num only [Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, zero_div]
    rw [show 0 - (2 * Real.pi / n + Real.pi / n) = -(3 * (Real.pi / n)) by ring,
      Real.cos_neg, antiprism_diagonal_increment hn]
  · rw [antiprism_cross_dist_sq hn]
    norm_num only [Nat.cast_ofNat, Nat.cast_zero, mul_zero, zero_div, zero_add]
    rw [show 2 * Real.pi * 2 / n - Real.pi / n = 3 * (Real.pi / n) by ring,
      antiprism_diagonal_increment hn]

end Uniform5.Composition
