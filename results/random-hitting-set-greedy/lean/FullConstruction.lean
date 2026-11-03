import ExpectationConstruction
import SourceConsequence

/-! The probability theorem and the refutation of Conjecture 12 on the
definitions of `Endpoint` and `SourceEndpoint`. -/
namespace ADG
open Finset

/-- Explicit positive rational gap and probability constants. -/
def gapConstant : ℚ := badDensity/8
def probabilityConstant : ℚ := badDensity/4
def constructionThreshold : ℕ := 10^20

lemma parameter_density_tail {k : ℕ} (hk : 14 ≤ k) :
    (badDensity : ℝ)/2 ≤ matrixProb k (k^10) (parameterP k)
      (fun A => ((badDensity : ℝ)/2)*(k : ℝ) ≤ (B A : ℝ)) := by
  have hkpos : 0 < k := by omega
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have he := expected_bad_middles_lower hk
  have h := badMiddles_tail_lower_bound k (k^10) (parameterP k) hkpos
    (parameterP_pos (by omega)).le (parameterP_le_one (by omega))
    (((badDensity : ℝ)/2)*(k : ℝ)) ((badDensity : ℝ)*(k : ℝ)) (by
      have hc : (0 : ℝ) < badDensity := by exact_mod_cast badDensity_pos
      positivity) he
  have heq : ((badDensity : ℝ)*(k : ℝ)-(badDensity : ℝ)/2*(k : ℝ))/(k : ℝ) =
      (badDensity : ℝ)/2 := by field_simp; ring
  rwa [heq] at h

lemma threshold_large_density {k : ℕ} (hk : constructionThreshold ≤ k) :
    2 ≤ ((badDensity : ℝ)/2)*(k : ℝ) := by
  have hk' : (10^20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  norm_num [badDensity]
  nlinarith

lemma threshold_exceptional_loss {k : ℕ} (hk : constructionThreshold ≤ k) :
    (1/(10000*(k : ℝ)^2) : ℝ)+160000/(k : ℝ)^2 ≤ (badDensity : ℝ)/4 := by
  have hk' : (10^20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have hksq : 0 < (k : ℝ)^2 := sq_pos_of_ne_zero hk0
  have hs : (10^20 : ℝ)^2 ≤ (k : ℝ)^2 := by nlinarith
  calc
    _ = (160000+1/10000)/(k : ℝ)^2 := by field_simp; ring
    _ ≤ _ := (div_le_iff₀ hksq).mpr (by norm_num [badDensity]; nlinarith)

/-- Complete positive-probability gap for every sufficiently large kth-power input. -/
theorem frozen_probability_endpoint : FrozenProbabilityEndpoint := by
  refine ⟨gapConstant,probabilityConstant,constructionThreshold,?_,?_,?_⟩
  · exact div_pos badDensity_pos (by norm_num)
  · exact div_pos badDensity_pos (by norm_num)
  intro k hk
  have hk14 : 14 ≤ k := by
    have ht : 14 ≤ constructionThreshold := by norm_num [constructionThreshold]
    omega
  have hk2 : 2 ≤ k := by omega
  have hp := (parameterP_pos (by omega : 1 ≤ k)).le
  have hp' := parameterP_le_one (by omega : 1 ≤ k)
  refine ⟨by omega,?_⟩
  have htail := parameter_density_tail hk14
  have hgood := matrixProb_joint_good_lower_bound k (k^10) (parameterP k) hp hp'
    (fun A => ((badDensity : ℝ)/2)*(k : ℝ) ≤ (B A : ℝ))
  have hn := parameter_noLarge_failure_bound (by omega : 1 ≤ k)
  have hpairs := parameter_allPairs_failure_bound hk2
  have hloss := threshold_exceptional_loss hk
  have hjoint : (probabilityConstant : ℝ) ≤ matrixProb k (k^10) (parameterP k)
      (fun A => ((badDensity : ℝ)/2)*(k : ℝ) ≤ (B A : ℝ) ∧
        noLargeColumns A ∧ allExactPairs A) := by
    norm_num [probabilityConstant] at *
    linarith
  apply le_trans hjoint
  apply matrixProb_mono _ _ _ hp hp'
  intro A hA
  refine ⟨exactPairs_feasible A hk2 hA.2.2,?_⟩
  have hc : (0 : ℝ) ≤ (badDensity : ℝ)/2 := by
    have hc : (0 : ℝ) < badDensity := by exact_mod_cast badDensity_pos
    positivity
  have hgap := actual_greedy_lp_gap_of_bad_density A hk2 hA.2.1 hA.2.2
    ((badDensity : ℝ)/2) hc hA.1 (threshold_large_density hk)
  convert hgap using 1 <;> norm_num [gapConstant] <;> ring <;> simp

/-- Full source-faithful refutation, including all-n hypotheses and arbitrary
infeasible-instance ratio conventions. No hypothesis of the refutation remains. -/
theorem full_frozen_endpoint : FullFrozenEndpoint :=
  assemble_full_endpoint frozen_probability_endpoint

end ADG
