/- Adapted from aravindkarthigeyan/thomson-n9-lean, proof/lean/ClaudeWindow/Geometry.lean
   MIT, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e. See certificate/Windows/LICENSE-N9. -/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ThomsonN10.Windows.WindowCheck

/-!
# Gram-determinant geometry in `ℝ³` (L3, window classification)

* `cross_gram_det_zero`: for any eight vectors `U 0..3`, `Z 0..3` in `ℝ³`, the 4×4
  cross-Gram determinant `det (⟪U α, Z β⟫)` vanishes (rank ≤ 3), proved by factoring
  through a 4×4 coordinate matrix with a zero row.
* `gram3_nonneg`: the 3×3 Gram determinant of unit vectors is `≥ 0` (it is a square).
* `pairR_eq_zero`, `normR_eq_zero`: the explicit bordered (Schur) forms used by the checker
  vanish on actual configurations.
-/

namespace ThomsonN10.Windows

open Matrix

abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem inner_coord (x y : E3) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- Coordinates of four vectors, padded to a 4×4 matrix by a zero last row. -/
def padM (U : Fin 4 → E3) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun k α => if h : (k : ℕ) < 3 then U α ⟨k, h⟩ else 0

theorem cross_gram_eq (U Z : Fin 4 → E3) :
    (Matrix.of fun α β => inner ℝ (U α) (Z β)) = (padM U)ᵀ * padM Z := by
  ext α β
  simp [Matrix.mul_apply, padM, Fin.sum_univ_four, inner_coord]

theorem cross_gram_det_zero (U Z : Fin 4 → E3) :
    (Matrix.of fun α β => inner ℝ (U α) (Z β)).det = 0 := by
  rw [cross_gram_eq, det_mul,
    det_eq_zero_of_row_eq_zero (A := padM Z) (3 : Fin 4) (fun j => by simp [padM]), mul_zero]

/-- Coordinates of three vectors as a 3×3 matrix (columns = vectors). -/
def coordM (U : Fin 3 → E3) : Matrix (Fin 3) (Fin 3) ℝ := fun k α => U α k

theorem gram_eq (U : Fin 3 → E3) :
    (Matrix.of fun α β => inner ℝ (U α) (U β)) = (coordM U)ᵀ * coordM U := by
  ext α β
  simp [Matrix.mul_apply, coordM, Fin.sum_univ_three, inner_coord]

theorem gram_det_nonneg (U : Fin 3 → E3) :
    0 ≤ (Matrix.of fun α β => inner ℝ (U α) (U β)).det := by
  rw [gram_eq, det_mul, det_transpose]
  exact mul_self_nonneg _

/-- The 3×3 Gram determinant of unit vectors, in the explicit form used throughout. -/
theorem gram3_nonneg (x y z : E3) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    0 ≤ d3R (inner ℝ x y) (inner ℝ x z) (inner ℝ y z) := by
  have h := gram_det_nonneg ![x, y, z]
  rw [det_fin_three] at h
  simp only [of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    hx, hy, hz, real_inner_comm x y, real_inner_comm x z, real_inner_comm y z] at h
  unfold d3R
  nlinarith [h]

/-- Explicit expansion of a 4×4 determinant along the first row. -/
theorem det4_expand (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M.det =
      M 0 0 * (M 1 1 * M 2 2 * M 3 3 - M 1 1 * M 2 3 * M 3 2 - M 1 2 * M 2 1 * M 3 3
        + M 1 2 * M 2 3 * M 3 1 + M 1 3 * M 2 1 * M 3 2 - M 1 3 * M 2 2 * M 3 1)
    - M 0 1 * (M 1 0 * M 2 2 * M 3 3 - M 1 0 * M 2 3 * M 3 2 - M 1 2 * M 2 0 * M 3 3
        + M 1 2 * M 2 3 * M 3 0 + M 1 3 * M 2 0 * M 3 2 - M 1 3 * M 2 2 * M 3 0)
    + M 0 2 * (M 1 0 * M 2 1 * M 3 3 - M 1 0 * M 2 3 * M 3 1 - M 1 1 * M 2 0 * M 3 3
        + M 1 1 * M 2 3 * M 3 0 + M 1 3 * M 2 0 * M 3 1 - M 1 3 * M 2 1 * M 3 0)
    - M 0 3 * (M 1 0 * M 2 1 * M 3 2 - M 1 0 * M 2 2 * M 3 1 - M 1 1 * M 2 0 * M 3 2
        + M 1 1 * M 2 2 * M 3 0 + M 1 2 * M 2 0 * M 3 1 - M 1 2 * M 2 1 * M 3 0) := by
  rw [det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, det_fin_three, submatrix_apply]
  simp [Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def]
  ring

/-- The cross-Gram determinant of `(p₀,p₁,p₂,y)` against `(p₀,p₁,p₂,z)` in bordered form.
Only the anchors need to be unit vectors. -/
theorem pairR_eq_zero (p0 p1 p2 y z : E3) (h0 : ‖p0‖ = 1) (h1 : ‖p1‖ = 1) (h2 : ‖p2‖ = 1) :
    pairR (inner ℝ p0 p1) (inner ℝ p0 p2) (inner ℝ p1 p2)
      (inner ℝ y p0) (inner ℝ y p1) (inner ℝ y p2)
      (inner ℝ p0 z) (inner ℝ p1 z) (inner ℝ p2 z) (inner ℝ y z) = 0 := by
  have h := cross_gram_det_zero ![p0, p1, p2, y] ![p0, p1, p2, z]
  rw [det4_expand] at h
  simp only [of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    h0, h1, h2, real_inner_comm p0 p1, real_inner_comm p0 p2, real_inner_comm p1 p2] at h
  unfold pairR d3R
  linear_combination h

/-- The 4×4 Gram determinant of unit vectors `(p₀,p₁,p₂,y)` in Schur form. -/
theorem normR_eq_zero (p0 p1 p2 y : E3) (h0 : ‖p0‖ = 1) (h1 : ‖p1‖ = 1) (h2 : ‖p2‖ = 1)
    (hy : ‖y‖ = 1) :
    normR (inner ℝ p0 p1) (inner ℝ p0 p2) (inner ℝ p1 p2)
      (inner ℝ y p0) (inner ℝ y p1) (inner ℝ y p2) = 0 := by
  have h := pairR_eq_zero p0 p1 p2 y y h0 h1 h2
  rw [real_inner_self_eq_norm_sq y, hy, real_inner_comm y p0, real_inner_comm y p1,
    real_inner_comm y p2] at h
  unfold pairR at h
  unfold normR
  linear_combination h

end ThomsonN10.Windows
