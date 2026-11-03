import Endpoint
import SourceEndpoint

/-! Greedy with fresh uniform tie-breaking among labelled maximizers, and the
statements proved in `UniformConstruction`. -/
namespace ADG.Uniform
open Finset Filter
open scoped Topology Classical

/-- Positive labelled maximizers. Previously picked columns have zero gain,
so including all labels gives precisely the remaining positive maximizers. -/
noncomputable def maximizers {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m)) :
    Finset (Fin n) := by
  classical
  exact univ.filter (fun j => 0 < gain A U j ∧ ∀ t, gain A U t ≤ gain A U j)

/-- Literal conditional uniform kernel, freshly applied at each recursive step.
Fuel m suffices: every selected column covers at least one new row.
The event is on the number of picks, rather than a uniform distribution on traces. -/
noncomputable def countProb {m n : ℕ} (A : Matrix m n) :
    ℕ → Finset (Fin m) → (ℕ → Prop) → ℝ
  | 0, _, event => if event 0 then 1 else 0
  | fuel + 1, U, event =>
    let J := maximizers A U
    if J = ∅ then (if event 0 then 1 else 0)
    else (∑ j ∈ J, countProb A fuel (U \ A j) (fun g => event (g+1))) / J.card

/-- Joint law of iid matrix and the conditional fresh uniform choices. -/
noncomputable def jointProb (m n : ℕ) (p : ℝ) (event : Matrix m n → ℕ → Prop) : ℝ :=
  ∑ A : Matrix m n, iidMass (columnMass m p) A * countProb A m univ (event A)

def good {m n : ℕ} (A : Matrix m n) : Prop := noLargeColumns A ∧ allExactPairs A

def c : ℚ := 1 / (196608 * 10^9)
def epsilon : ℚ := c/8
def eta : ℚ := c/8
def threshold : ℕ := 10^20

/-- Exact constants and threshold; no assumption about a coupling is a premise. -/
def UniformProbabilityEndpoint : Prop :=
  ∀ k ≥ threshold,
    (eta : ℝ) ≤ jointProb k (k^10) (parameterP k)
      (fun A g => feasible A ∧ (1 + (epsilon : ℝ)) * L A ≤ (g : ℝ))

noncomputable def ratio
    (infeasibleValue : ∀ n, Matrix (sourceM n) n → ℝ)
    (n : ℕ) (A : Matrix (sourceM n) n) (g : ℕ) : ℝ := by
  classical
  exact if feasible A then (g : ℝ) / L A else infeasibleValue n A

def RatioConvergesToOne
    (infeasibleValue : ∀ n, Matrix (sourceM n) n → ℝ) : Prop :=
  ∀ e : ℝ, 0 < e →
    Tendsto (fun n => jointProb (sourceM n) n (sourceP n)
      (fun A g => e ≤ |ratio infeasibleValue n A g - 1|)) atTop (𝓝 0)

def FullUniformEndpoint : Prop :=
  UniformProbabilityEndpoint ∧ SourceAdmissible ∧
  (∀ k, sourceM (k^10) = k ∧ sourceP (k^10) = parameterP k) ∧
  Tendsto (fun n => (sourceM n : ℝ) * sourceP n) atTop (𝓝 0) ∧
  ∀ infeasibleValue, ¬ RatioConvergesToOne infeasibleValue

end ADG.Uniform
