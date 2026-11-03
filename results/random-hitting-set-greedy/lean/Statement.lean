import FullConstruction
import UniformConstruction

/-! The theorems in the paper, with the definitions they rest on spelled out. -/
open ADG Finset

namespace GreedyLPHittingSet

/-- Theorem 1 of the paper, leftmost ties, with explicit constants:
for every k ≥ 10^20, with m = k, n = k^10 and p = 1/(10k^4), the matrix is
feasible and G ≥ (1 + c/8) L with probability at least c/4. -/
theorem leftmost_explicit : ∀ k ≥ Uniform.threshold,
    (Uniform.c : ℝ) / 4 ≤ matrixProb k (k^10) (parameterP k)
      (fun A => feasible A ∧ (1 + (Uniform.epsilon : ℝ)) * L A ≤ (G A : ℝ)) := by
  intro k hk
  have hk1 : 1 ≤ k := le_trans (by norm_num [Uniform.threshold]) hk
  exact le_trans (Uniform.leftmost_good_gap hk)
    (matrixProb_mono _ _ _ (parameterP_pos hk1).le (parameterP_le_one hk1)
      (fun _ hA => hA.2))

end GreedyLPHittingSet

-- The constants.
example : Uniform.c = 1 / (196608 * 10^9) := rfl
example : Uniform.epsilon = Uniform.c / 8 := rfl
example : Uniform.eta = Uniform.c / 8 := rfl
example : Uniform.threshold = 10^20 := rfl
example (k : ℕ) : parameterP k = 1 / (10 * (k : ℝ)^4) := rfl

-- The random matrix: column supports with independent Bernoulli(p) entries.
example (m : ℕ) (p : ℝ) (s : Finset (Fin m)) :
    columnMass m p s = ∏ i, if i ∈ s then p else 1 - p := rfl
example (m n : ℕ) (p : ℝ) (E : ADG.Matrix m n → Prop) [DecidablePred E] :
    matrixProb m n p E = ∑ A : ADG.Matrix m n, if E A then ∏ j, columnMass m p (A j) else 0 := by
  unfold matrixProb iidProb iidMass
  congr 1
  funext A
  congr

-- Feasibility, the LP and Greedy.
example {m n : ℕ} (A : ADG.Matrix m n) : feasible A ↔ ∀ i, ∃ j, i ∈ A j := Iff.rfl
example {m n : ℕ} (A : ADG.Matrix m n) :
    L A = sInf ((fun x : Fin n → ℝ => ∑ j, x j) ''
      {x | (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ ∀ i, 1 ≤ ∑ j, if i ∈ A j then x j else 0}) := rfl
example {m n : ℕ} (A : ADG.Matrix m n) : G A = (trace A m univ).length := rfl
example {m n : ℕ} (A : ADG.Matrix m n) (U : Finset (Fin m)) (j : Fin n) :
    gain A U j = (U ∩ A j).card := rfl

-- Fresh uniform ties: the positive maximizers and the conditional kernel.
example {m n : ℕ} (A : ADG.Matrix m n) (U : Finset (Fin m)) (j : Fin n) :
    j ∈ Uniform.maximizers A U ↔ 0 < gain A U j ∧ ∀ t, gain A U t ≤ gain A U j := by
  simp [Uniform.maximizers]

-- The theorems' types.
example : FrozenProbabilityEndpoint := frozen_probability_endpoint
example : FullFrozenEndpoint := full_frozen_endpoint
example : Uniform.UniformProbabilityEndpoint := Uniform.uniform_probability_endpoint
example : Uniform.FullUniformEndpoint := Uniform.full_uniform_endpoint
example : SourceAdmissible := source_admissible
example : ∀ v : ∀ n : ℕ, ADG.Matrix (sourceM n) n → ℝ, ¬ SourceRatioConvergesToOne v :=
  full_frozen_endpoint.2.2.2.2.2
example : ∀ v : ∀ n : ℕ, ADG.Matrix (sourceM n) n → ℝ, ¬ Uniform.RatioConvergesToOne v :=
  Uniform.full_uniform_endpoint.2.2.2.2
