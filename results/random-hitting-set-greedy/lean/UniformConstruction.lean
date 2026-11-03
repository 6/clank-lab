import UniformGoodLaw

/-! The theorem for fresh uniform tie-breaking, derived from the leftmost
theorem by an exact transport. -/
namespace ADG.Uniform
open Finset Filter
open scoped Classical Topology

/-- Exposes the joint-good bound already inside the original construction proof. -/
theorem leftmost_good_gap {k : ℕ} (hk : threshold ≤ k) :
    (c : ℝ)/4 ≤ matrixProb k (k^10) (parameterP k)
      (fun A => good A ∧ feasible A ∧ (1+(epsilon : ℝ))*L A ≤ (G A : ℝ)) := by
  have hk14 : 14 ≤ k := by
    have ht : 14 ≤ threshold := by norm_num [threshold]
    omega
  have hk2 : 2 ≤ k := by omega
  have hp := (parameterP_pos (by omega : 1 ≤ k)).le
  have hp' := parameterP_le_one (by omega : 1 ≤ k)
  have htail := parameter_density_tail hk14
  have hgood := matrixProb_joint_good_lower_bound k (k^10) (parameterP k) hp hp'
    (fun A => ((badDensity : ℝ)/2)*(k : ℝ) ≤ (B A : ℝ))
  have hn := parameter_noLarge_failure_bound (by omega : 1 ≤ k)
  have hpairs := parameter_allPairs_failure_bound hk2
  have hkc : constructionThreshold ≤ k := hk
  have hloss := threshold_exceptional_loss hkc
  have hjoint : (c : ℝ)/4 ≤ matrixProb k (k^10) (parameterP k)
      (fun A => ((badDensity : ℝ)/2)*(k : ℝ) ≤ (B A : ℝ) ∧
        noLargeColumns A ∧ allExactPairs A) := by
    norm_num [c, badDensity] at *
    linarith
  apply le_trans hjoint
  apply matrixProb_mono _ _ _ hp hp'
  intro A hA
  refine ⟨hA.2, exactPairs_feasible A hk2 hA.2.2, ?_⟩
  have hc : (0 : ℝ) ≤ (badDensity : ℝ)/2 := by
    have hc : (0 : ℝ) < badDensity := by exact_mod_cast badDensity_pos
    positivity
  have hgap := actual_greedy_lp_gap_of_bad_density A hk2 hA.2.1 hA.2.2
    ((badDensity : ℝ)/2) hc hA.1 (threshold_large_density hkc)
  convert hgap using 1 <;> norm_num [epsilon, c, badDensity]

/-- Literal fresh uniform labelled ties, with the exact constants. -/
theorem uniform_probability_endpoint : UniformProbabilityEndpoint := by
  intro k hk
  have hk1 : 1 ≤ k := by
    have ht : 1 ≤ threshold := by norm_num [threshold]
    omega
  have hp := (parameterP_pos hk1).le
  have hp' := parameterP_le_one hk1
  have he : jointProb k (k^10) (parameterP k)
      (fun A g => good A ∧ feasible A ∧ (1+(epsilon : ℝ))*L A ≤ (g : ℝ)) =
      matrixProb k (k^10) (parameterP k)
        (fun A => good A ∧ feasible A ∧ (1+(epsilon : ℝ))*L A ≤ (G A : ℝ)) := by
    apply joint_good_transport
    intro A π g
    rw [L_relabel]
  have hlow := leftmost_good_gap hk
  have heta : (eta : ℝ) ≤ (c : ℝ)/4 := by norm_num [eta, c]
  apply (heta.trans hlow).trans
  rw [← he]
  apply jointProb_mono _ _ _ hp hp'
  intro A g hA
  exact hA.2

lemma ratio_gap {n : ℕ} (hn : 0 < sourceM n)
    (v : ∀ n, Matrix (sourceM n) n → ℝ) (A : Matrix (sourceM n) n) (g : ℕ)
    (hA : feasible A ∧ (1+(epsilon : ℝ))*L A ≤ (g : ℝ)) :
    (epsilon : ℝ) ≤ |ratio v n A g - 1| := by
  have hL := lp_pos A hn hA.1
  have hrat : 1+(epsilon : ℝ) ≤ (g : ℝ)/L A := (le_div_iff₀ hL).mpr hA.2
  rw [ratio, if_pos hA.1]
  exact le_trans (by linarith : (epsilon : ℝ) ≤ (g : ℝ)/L A-1) (le_abs_self _)

theorem uniform_ratio_failure (v : ∀ n, Matrix (sourceM n) n → ℝ) :
    ¬ RatioConvergesToOne v := by
  intro hc
  have hη : (0 : ℝ) < eta := by norm_num [eta, c]
  have hε : (0 : ℝ) < epsilon := by norm_num [epsilon, c]
  have hs : ∀ᶠ n : ℕ in atTop,
      jointProb (sourceM n) n (sourceP n)
        (fun A g => (epsilon : ℝ) ≤ |ratio v n A g - 1|) < eta :=
    (hc (epsilon : ℝ) hε).eventually (eventually_lt_nhds hη)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hs
  let k := max threshold (N+1)
  have hk : threshold ≤ k := le_max_left _ _
  have hkN : N+1 ≤ k := le_max_right _ _
  have hkp : 0 < k := by
    have ht : 0 < threshold := by norm_num [threshold]
    omega
  have hpow : k ≤ k^10 := Nat.le_self_pow (by norm_num) _
  have hn : 1 ≤ k^10 := by omega
  have hm : 0 < sourceM (k^10) := by rw [sourceM_agrees]; exact hkp
  have hgap : (eta : ℝ) ≤ jointProb (sourceM (k^10)) (k^10) (sourceP (k^10))
      (fun A g => feasible A ∧ (1+(epsilon : ℝ))*L A ≤ (g : ℝ)) := by
    rw [sourceM_agrees, sourceP_agrees]
    exact uniform_probability_endpoint k hk
  have hlow : (eta : ℝ) ≤ jointProb (sourceM (k^10)) (k^10) (sourceP (k^10))
      (fun A g => (epsilon : ℝ) ≤ |ratio v (k^10) A g - 1|) := by
    apply le_trans hgap
    apply jointProb_mono _ _ _ (sourceP_nonneg _)
      (le_trans (sourceP_le_half hn) (by norm_num))
    exact fun A g hA => ratio_gap hm v A g hA
  exact (not_lt_of_ge hlow) (hN (k^10) (by omega))

/-- Source hypotheses hold for every n; the obstruction uses only n=k^10. -/
theorem full_uniform_endpoint : FullUniformEndpoint :=
  ⟨uniform_probability_endpoint, source_admissible,
    fun k => ⟨sourceM_agrees k, sourceP_agrees k⟩,
    sourceMP_tendsto_zero, uniform_ratio_failure⟩

end ADG.Uniform
