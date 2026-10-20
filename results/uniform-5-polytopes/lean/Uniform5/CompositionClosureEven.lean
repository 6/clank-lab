import Uniform5.CompositionReciprocalClassHull
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Group.EvenFunction

/-! The literal closure function is even. Thus its derivative at reciprocal
zero vanishes, including Mathlib's nondifferentiable fallback case. -/
noncomputable section
namespace Uniform5.Composition

@[simp] theorem cyclePolarCosine_neg (ρ d s : ℝ) :
    cyclePolarCosine ρ d (-s) = -cyclePolarCosine ρ d s := by
  simp only [cyclePolarCosine, neg_sq, mul_neg, neg_div]

@[simp] theorem closureArgument_neg (ρ d e α s : ℝ) :
    closureArgument ρ d e α (-s) = closureArgument ρ d e α s := by
  simp only [closureArgument, cyclePolarCosine_neg, neg_mul_neg, neg_sq]

@[simp] theorem closureSummand_neg (ρ d e α s : ℝ) :
    closureSummand ρ d e α (-s) = closureSummand ρ d e α s := by
  simp only [closureSummand, cyclePolarCosine_neg, neg_mul_neg, neg_sq]

theorem finiteCycleClosure_even {n : ℕ} (ρ : ℝ) (d α : Fin n → ℝ) :
    Function.Even (finiteCycleClosure ρ d α) := by
  intro s
  simp only [finiteCycleClosure, closureSummand_neg]

theorem LibraryCycleClass.closure_even (W : LibraryCycleClass) (N : LibraryNumericalData) :
    Function.Even (W.closure N) := by
  rcases W with ⟨k, n, W⟩
  refine Quotient.inductionOn W ?_
  intro V
  exact finiteCycleClosure_even _ _ _

theorem even_deriv_zero {f : ℝ → ℝ} (hf : Function.Even f) : deriv f 0 = 0 := by
  have heq : (fun s => f (-s)) = f := funext hf
  have h := deriv_comp_neg (f := f) (x := 0)
  rw [heq, neg_zero] at h
  linarith

theorem LibraryCycleClass.closure_deriv_zero (W : LibraryCycleClass) (N : LibraryNumericalData) :
    deriv (W.closure N) 0 = 0 := even_deriv_zero (W.closure_even N)

/-- The whole-class derivative exclusion of ROOT forces a positive lower
reciprocal endpoint whenever that class carries a signature. -/
theorem class_lower_pos_of_derivative_exclusion (S : StageOneNumericalData)
    (c : ActiveRootClass S) (W : LibraryCycleClass) (N : LibraryNumericalData)
    (hderiv : ∀ s ∈ (reciprocalClassHull S c).carrier, deriv (W.closure N) s ≠ 0) :
    0 < (reciprocalClassHull S c).lo := by
  have hlo := reciprocalClassHull_lo_nonneg S c
  by_contra h
  have hz : (reciprocalClassHull S c).lo = 0 := le_antisymm (le_of_not_gt h) hlo
  have hm : (0 : ℝ) ∈ (reciprocalClassHull S c).carrier :=
    ⟨hz.le, (reciprocalClassHull_hi_pos S c).le⟩
  exact hderiv 0 hm (W.closure_deriv_zero N)

end Uniform5.Composition
