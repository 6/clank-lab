import ABC.S4.R2Aux5

/-! R2 helpers: the Floquet matrix `Q(t) = X(t) S R(-νt)`, extended 2π-periodically to the strip. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)
open scoped ContDiff NNReal

noncomputable section

namespace ABC.S4.R2Aux

open ABC ABC.S4

/-- `R(z) = e^{zJ}`. -/
def Rm (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.cos z, Complex.sin z; -Complex.sin z, Complex.cos z]

def Jm : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem Rm_add (a b : ℂ) : Rm a * Rm b = Rm (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rm, Matrix.mul_apply, Fin.sum_univ_two, Complex.cos_add, Complex.sin_add] <;> ring

theorem Rm_zero : Rm 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Rm]

theorem det_Rm (z : ℂ) : (Rm z).det = 1 := by
  simp [Rm, Matrix.det_fin_two]; rw [← Complex.sin_sq_add_cos_sq z]; ring

theorem hasDerivAt_mat_mul {A B : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {A' B' : Matrix (Fin 2) (Fin 2) ℂ}
    {t : ℂ} (hA : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun t => B t i j) (B' i j) t) (i j : Fin 2) :
    HasDerivAt (fun t => (A t * B t) i j) ((A' * B t + A t * B') i j) t := by
  have : HasDerivAt (fun t => ∑ k, A t i k * B t k j)
      (∑ k, (A' i k * B t k j + A t i k * B' k j)) t :=
    HasDerivAt.fun_sum fun k _ => (hA i k).mul (hB k j)
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using this

theorem hasDerivAt_Rm (ν : ℂ) (t : ℂ) (i j : Fin 2) :
    HasDerivAt (fun t => Rm (-ν * t) i j) ((-ν) • (Rm (-ν * t) * Jm) i j) t := by
  have h : HasDerivAt (fun y => -ν * y) (-ν) t := by
    simpa using (hasDerivAt_id' t).const_mul (-ν)
  have hc := h.ccos
  have hs := h.csin
  fin_cases i <;> fin_cases j
  · refine hc.congr_deriv ?_; simp [Rm, Jm, Matrix.mul_apply, Fin.sum_univ_two]; ring
  · refine hs.congr_deriv ?_; simp [Rm, Jm, Matrix.mul_apply, Fin.sum_univ_two]; ring
  · refine hs.neg.congr_deriv ?_; simp [Rm, Jm, Matrix.mul_apply, Fin.sum_univ_two]; ring
  · refine hc.congr_deriv ?_; simp [Rm, Jm, Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem Rm_Jm (z : ℂ) : Rm z * Jm = Jm * Rm z := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Rm, Jm, Matrix.mul_apply, Fin.sum_univ_two]

theorem Rm_real (x : ℝ) (i j : Fin 2) : (Rm x i j).im = 0 := by
  fin_cases i <;> fin_cases j <;> simp [Rm, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The real normal form, read as complex matrices. -/
structure NF (M : Matrix (Fin 2) (Fin 2) ℂ) (S : Matrix (Fin 2) (Fin 2) ℂ) (ν : ℝ) : Prop where
  conjS : M * S = S * Rm (2 * π * ν)
  det : S.det = 1
  real : ∀ i j, (S i j).im = 0

theorem exists_NF {M : Matrix (Fin 2) (Fin 2) ℂ} (hre : ∀ i j, (M i j).im = 0)
    (hdet : M.det = 1) (htr : |(M 0 0 + M 1 1).re| < 2) :
    ∃ S ν, NF M S ν ∧ Real.cos (2 * π * ν) = (M 0 0 + M 1 1).re / 2 := by
  have hM : ∀ i j, M i j = ((M i j).re : ℂ) := fun i j => by
    apply Complex.ext <;> simp [hre]
  have hdet' : (M 0 0).re * (M 1 1).re - (M 0 1).re * (M 1 0).re = 1 := by
    have := congrArg Complex.re hdet
    rw [Matrix.det_fin_two] at this
    simpa [hre] using this
  obtain ⟨a, b, c, d, θ, hS, hcos, e1, e2, e3, e4⟩ :=
    elliptic_normal_form _ _ _ _ hdet' (by simpa using htr)
  have hMeq : M = !![((M 0 0).re : ℂ), (M 0 1).re; (M 1 0).re, (M 1 1).re] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [← hM]
  have c1 := congrArg (fun x : ℝ => (x : ℂ)) e1
  have c2 := congrArg (fun x : ℝ => (x : ℂ)) e2
  have c3 := congrArg (fun x : ℝ => (x : ℂ)) e3
  have c4 := congrArg (fun x : ℝ => (x : ℂ)) e4
  push_cast at c1 c2 c3 c4
  have h2π : 2 * π * (θ / (2 * π)) = θ := by field_simp
  refine ⟨!![(a : ℂ), b; c, d], θ / (2 * π), ⟨?_, ?_, ?_⟩, ?_⟩
  · have hθ : (2 * π * ((θ / (2 * π) : ℝ) : ℂ)) = (θ : ℂ) := by
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      push_cast; field_simp
    rw [hθ, hMeq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Rm, Matrix.mul_apply, Fin.sum_univ_two, Complex.ofReal_cos, Complex.ofReal_sin]
    · linear_combination c1
    · linear_combination c2
    · linear_combination c3
    · linear_combination c4
  · rw [Matrix.det_fin_two_of]; exact_mod_cast hS
  · intro i j; fin_cases i <;> fin_cases j <;> simp
  · rw [h2π, hcos]; simp

end ABC.S4.R2Aux
