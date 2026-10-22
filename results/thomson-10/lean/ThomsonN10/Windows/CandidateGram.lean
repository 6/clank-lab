/- Adapted from aravindkarthigeyan/thomson-n9-lean,
   proof/lean/ClaudeWindow/CandidateGram.lean, MIT,
   commit 168ff0c98cab4dfda0460ba55f8d169070ac385e. -/
import ThomsonN10.Windows.WindowBoxes
import ThomsonN10.Windows.Geometry

namespace ThomsonN10.Windows

theorem vec_inner (a b c d e f : ℝ) :
    inner ℝ (vec a b c) (vec d e f) = a*d+b*e+c*f := by
  simp [inner_coord, vec]

theorem refColor_lt7 : ∀ i, i < 10 → ∀ j, j < 10 → i ≠ j → refColor i j < 7 := by decide

theorem candidateAt_inner {h : ℝ} (hh : hBox.Mem h) (i j : Fin 10) (hij : i ≠ j) :
    inner ℝ (candidateAt h i) (candidateAt h j) = palette h (refColor i j) := by
  have h0 : 0 < h := lt_of_lt_of_le (by norm_num [hBox]) hh.1
  have h1 : h < 1 := lt_of_le_of_lt hh.2 (by norm_num [hBox])
  have hs : Real.sqrt (2 : ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : rho h ^ 2 = 1-h^2 := Real.sq_sqrt (by nlinarith)
  fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij <;>
    simp [candidateAt, vec_inner, refColor, palette, q] <;> ring_nf <;>
    simp only [hs, hz] <;> ring

theorem candidateAt_inner_self {h : ℝ} (hh : hBox.Mem h) (i : Fin 10) :
    inner ℝ (candidateAt h i) (candidateAt h i) = 1 := by
  have h0 : 0 < h := lt_of_lt_of_le (by norm_num [hBox]) hh.1
  have h1 : h < 1 := lt_of_le_of_lt hh.2 (by norm_num [hBox])
  have hs : Real.sqrt (2 : ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : rho h ^ 2 = 1-h^2 := Real.sq_sqrt (by nlinarith)
  rw [inner_coord]
  fin_cases i <;> simp [candidateAt, vec, q] <;> ring_nf <;>
    simp only [hs, hz] <;> ring

end ThomsonN10.Windows
