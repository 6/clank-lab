import Endpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The source's assumptions and the convergence statement. Assumption 2(3)
uses the same c/C as coefficient and exponent, as printed. -/
namespace ADG
open Filter
open scoped Topology

def SourceAdmissible : Prop :=
  ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ δ < 1 ∧
    ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ)^c ≤ (sourceM n : ℝ) ∧
      (sourceM n : ℝ) ≤ C * (n : ℝ)^C ∧
      1 / (n : ℝ)^δ ≤ sourceP n ∧ sourceP n ≤ 1/2

noncomputable def sourceRatio
    (infeasibleValue : ∀ n : ℕ, Matrix (sourceM n) n → ℝ)
    (n : ℕ) (A : Matrix (sourceM n) n) : ℝ := by
  classical
  exact if feasible A then (G A : ℝ) / L A else infeasibleValue n A

def SourceRatioConvergesToOne
    (infeasibleValue : ∀ n : ℕ, Matrix (sourceM n) n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => matrixProb (sourceM n) n (sourceP n)
      (fun A => ε ≤ |sourceRatio infeasibleValue n A - 1|)) atTop (𝓝 0)

/-- The full statement includes the central probability theorem and all source transport.
The infeasible convention is universally quantified and hence cannot affect refutation. -/
def FullFrozenEndpoint : Prop :=
  FrozenProbabilityEndpoint ∧ SourceAdmissible ∧
  (∀ k : ℕ, 0 < k → sourceM (k^10) = k ∧ sourceP (k^10) = parameterP k) ∧
  Tendsto (fun n => (sourceM n : ℝ) * sourceP n) atTop (𝓝 0) ∧
  SourceNonconvergence ∧
  ∀ infeasibleValue, ¬ SourceRatioConvergesToOne infeasibleValue

end ADG
