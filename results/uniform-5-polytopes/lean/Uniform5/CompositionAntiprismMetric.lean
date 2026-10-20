import Uniform5.CompositionCaseBModelRadii
import Uniform5.CompositionPolygonNeighborPair

/-! Exact coordinate metrics of the concrete antiprism. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

/-- Cylindrical coordinates separate angular and vertical distances. -/
theorem cylinder_dist_sq (r θ φ z w : ℝ) :
    dist (!₂[r * Real.cos θ, r * Real.sin θ, z] : Space 3)
      (!₂[r * Real.cos φ, r * Real.sin φ, w] : Space 3) ^ 2 =
      2 * r ^ 2 * (1 - Real.cos (θ - φ)) + (z - w) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Real.cos_sub]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_two, PiLp.sub_apply,
    WithLp.equiv_symm_pi_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons, Real.norm_eq_abs, sq_abs,
    Fin.sum_univ_zero, add_zero]
  nlinarith [congrArg (fun t : ℝ => r ^ 2 * t) (Real.sin_sq_add_cos_sq θ),
    congrArg (fun t : ℝ => r ^ 2 * t) (Real.sin_sq_add_cos_sq φ)]

/-- The height normalization is exactly the complement of the half-step
horizontal chord needed for unit cross-layer edges. -/
theorem antiprismHeight_sq_cos {n : ℕ} (hn : 3 ≤ n) :
    antiprismHeight n ^ 2 = 1 - 2 * unitPolygonRadius n ^ 2 * (1 - Real.cos (Real.pi / n)) := by
  have hh : 0 ≤ 1 - (2 * unitPolygonRadius n * Real.sin (Real.pi / (2 * n))) ^ 2 :=
    le_of_lt (Real.sqrt_pos.mp (antiprismHeight_pos hn))
  rw [antiprismHeight, Real.sq_sqrt hh]
  have he : Real.pi / n = 2 * (Real.pi / (2 * n)) := by ring
  rw [he, Real.cos_two_mul]
  nlinarith [congrArg (fun t : ℝ => 4 * unitPolygonRadius n ^ 2 * t)
    (Real.sin_sq_add_cos_sq (Real.pi / (2 * n)))]

/-- Every listed generator is an actual extreme point. -/
theorem antiprism_extremePoints (n : ℕ) :
    (antiprismModel n).extremePoints ℝ =
      Set.range (fun p : Bool × Fin n => antiprismPoint n p.1 p.2) := by
  apply Set.Subset.antisymm extremePoints_convexHull_subset
  apply CaseB.cospherical_extremePoints
    (c := (0 : Space 3)) (R := Real.sqrt (unitPolygonRadius n ^ 2 + (antiprismHeight n / 2) ^ 2))
  rintro _ ⟨⟨b, i⟩, rfl⟩
  rw [Metric.mem_sphere, dist_zero_right]
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [antiprismPoint_norm_sq, Real.sq_sqrt (by positivity)]
  ring

/-- The exact distance between an upper and lower indexed vertex. -/
theorem antiprism_cross_dist_sq {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    dist (antiprismPoint n false i) (antiprismPoint n true j) ^ 2 =
      1 + 2 * unitPolygonRadius n ^ 2 *
        (Real.cos (Real.pi / n) - Real.cos
          (2 * Real.pi * (i : ℕ) / n - (2 * Real.pi * (j : ℕ) / n + Real.pi / n))) := by
  unfold antiprismPoint
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [cylinder_dist_sq]
  have he : antiprismHeight n / 2 - -(antiprismHeight n / 2) = antiprismHeight n := by ring
  rw [he, antiprismHeight_sq_cos hn]
  ring

/-- Cross-layer edges separated by half a polygon step are unit segments. -/
theorem antiprism_cross_same_dist {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    dist (antiprismPoint n false i) (antiprismPoint n true i) = 1 := by
  apply (sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [antiprism_cross_dist_sq hn]
  have he : 2 * Real.pi * (i : ℕ) / n -
      (2 * Real.pi * (i : ℕ) / n + Real.pi / n) = -(Real.pi / n) := by ring
  rw [he, Real.cos_neg]
  ring

/-- The other adjacent cross-layer edge at upper vertex one is also unit. -/
theorem antiprism_cross_one_zero_dist {n : ℕ} (hn : 3 ≤ n) :
    dist (antiprismPoint n false ⟨1, by omega⟩) (antiprismPoint n true ⟨0, by omega⟩) = 1 := by
  apply (sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [antiprism_cross_dist_sq hn]
  norm_num only [Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, zero_div, zero_add]
  have he : 2 * Real.pi / n - Real.pi / n = Real.pi / n := by ring
  rw [he]
  ring

end Uniform5.Composition
