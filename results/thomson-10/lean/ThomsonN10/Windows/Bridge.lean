/- Adapted from aravindkarthigeyan/thomson-n9-lean,
   proof/lean/ClaudeWindow/Bridge.lean, MIT,
   commit 168ff0c98cab4dfda0460ba55f8d169070ac385e. -/
import ThomsonN10.Interfaces
import ThomsonN10.Windows.CandidateGram
import ThomsonN10.Windows.Main

namespace ThomsonN10.Windows

/-- Coherent seven-window classification, with the interface's exact radius and type. -/
theorem WindowClassification_holds : ThomsonN10.Interfaces.WindowClassification := by
  intro h x hx hwin
  have hh := parameter_mem h
  have hwin' : ∀ i j, i ≠ j → ∃ c : ℕ, c < 7 ∧
      |inner ℝ (x i) (x j) - palette h c| ≤ (windowRadius : ℝ) := by
    intro i j hij
    obtain ⟨c, hc⟩ := hwin i j hij
    refine ⟨c, c.isLt, ?_⟩
    rw [palette_contact]
    exact le_of_lt hc
  obtain ⟨σ, hσ⟩ := window_rigidity hh x hx.1 hwin'
  refine ⟨σ.symm, fun i j => ?_⟩
  by_cases hij : i = j
  · subst j
    rw [real_inner_self_eq_norm_sq, hx.1, one_pow]
    change |1 - inner ℝ (candidateAt h i) (candidateAt h i)| ≤ (windowRadius : ℝ)
    rw [candidateAt_inner_self hh, sub_self, abs_zero]
    norm_num [windowRadius]
  · have hp : σ.symm i ≠ σ.symm j := fun he => hij (σ.symm.injective he)
    have H := hσ (σ.symm i) (σ.symm j) hp
    rw [σ.apply_symm_apply, σ.apply_symm_apply] at H
    change |inner ℝ (x (σ.symm i)) (x (σ.symm j)) -
      inner ℝ (candidateAt h i) (candidateAt h j)| ≤ (windowRadius : ℝ)
    rw [candidateAt_inner hh i j hij]
    exact H

#print axioms WindowClassification_holds

end ThomsonN10.Windows
