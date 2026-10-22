/- Adapted from global-soundness/n10/project/Thomson10Soundness/SDP/CircleKernel.lean (supplied accepted N10 port of proof/lean/ThomsonN9/SDP/CircleKernel.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, MIT). -/
import ThomsonN10.Cert.SDP.Summation

namespace ThomsonN10.Cert.SDP
open ThomsonN10 ThomsonN10.Interfaces

noncomputable def circleKernel (a b : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => a
  | n+2 => 2*a*circleKernel a b (n+1)-b*circleKernel a b n

theorem circleKernel_eq_re_pow (z : ℂ) (n : ℕ) :
    circleKernel z.re (Complex.normSq z) n = (z^n).re := by
  induction n using Nat.twoStepInduction with
  | zero => simp [circleKernel]
  | one => simp [circleKernel]
  | more n ih₀ ih₁ =>
    rw [circleKernel, ih₀, ih₁]
    exact (complex_power_recurrence z n).symm

theorem circleKernel_gram_nonneg {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (a : ι → ℝ) (n : ℕ) :
    0 ≤ ∑ i, ∑ j, a i*a j*
      circleKernel (z i * star (z j)).re (Complex.normSq (z i * star (z j))) n := by
  have h := complex_gram_sum_nonneg (fun i => (a i : ℂ)*z i^n)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [circleKernel_eq_re_pow, mul_pow]
  have heq : ((a i : ℂ)*z i^n)*star ((a j : ℂ)*z j^n) =
      ((a i*a j : ℝ) : ℂ)*(z i^n*star (z j)^n) := by
    simp only [star_mul, star_pow, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [heq]
  simp

end ThomsonN10.Cert.SDP
