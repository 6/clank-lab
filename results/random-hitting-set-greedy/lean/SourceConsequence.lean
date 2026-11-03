import SourceTransport
import PathProbability

/-! From the probability theorem to the failure of convergence in probability. -/
namespace ADG
open Finset Filter
open scoped Topology

 theorem frozen_implies_source_nonconvergence
    (h : FrozenProbabilityEndpoint) : SourceNonconvergence := by
  obtain ⟨ε,η,k₀,hε,hη,h⟩ := h
  refine ⟨ε,η,hε,hη,?_⟩
  intro N
  let k := max k₀ (N+1)
  have hk : k₀ ≤ k := le_max_left _ _
  obtain ⟨hkpos,hprob⟩ := h k hk
  refine ⟨k^10, ?_, ?_⟩
  · have hkN : N+1 ≤ k := le_max_right _ _
    have hpow : k ≤ k^10 := Nat.le_self_pow (by norm_num) _
    omega
  · rw [sourceM_agrees,sourceP_agrees]
    exact hprob

 theorem sourceRatio_gap {n : ℕ} (hn : 0 < sourceM n)
    (v : ∀ n : ℕ, Matrix (sourceM n) n → ℝ)
    (ε : ℚ) (hε : 0 < ε) (A : Matrix (sourceM n) n)
    (hA : feasible A ∧ (1+(ε : ℝ))*L A ≤ (G A : ℝ)) :
    (ε : ℝ) ≤ |sourceRatio v n A - 1| := by
  have hL : 0 < L A := lp_pos A hn hA.1
  have hratio : 1+(ε : ℝ) ≤ (G A : ℝ)/L A :=
    (le_div_iff₀ hL).mpr hA.2
  have hdiff : (ε : ℝ) ≤ (G A : ℝ)/L A-1 := by linarith
  rw [sourceRatio, if_pos hA.1]
  exact le_trans hdiff (le_abs_self _)

 theorem frozen_implies_source_ratio_failure (h : FrozenProbabilityEndpoint)
    (v : ∀ n : ℕ, Matrix (sourceM n) n → ℝ) :
    ¬ SourceRatioConvergesToOne v := by
  obtain ⟨ε,η,k₀,hε,hη,h⟩ := h
  intro hc
  have hηr : (0 : ℝ) < η := by exact_mod_cast hη
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hs : ∀ᶠ n : ℕ in atTop,
      matrixProb (sourceM n) n (sourceP n)
        (fun A => (ε : ℝ) ≤ |sourceRatio v n A - 1|) < η :=
    (hc (ε : ℝ) hεr).eventually (eventually_lt_nhds hηr)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hs
  let k := max k₀ (N+1)
  have hk₀ : k₀ ≤ k := le_max_left _ _
  have hkN : N+1 ≤ k := le_max_right _ _
  obtain ⟨hk,hprob⟩ := h k hk₀
  have hpow : k ≤ k^10 := Nat.le_self_pow (by norm_num) _
  have hn : 1 ≤ k^10 := by omega
  have hsourcepos : 0 < sourceM (k^10) := by rw [sourceM_agrees]; exact hk
  have hgap : (η : ℝ) ≤ matrixProb (sourceM (k^10)) (k^10) (sourceP (k^10))
      (fun A => feasible A ∧ (1+(ε : ℝ))*L A ≤ (G A : ℝ)) := by
    rw [sourceM_agrees,sourceP_agrees]
    exact hprob
  have hlow : (η : ℝ) ≤ matrixProb (sourceM (k^10)) (k^10) (sourceP (k^10))
      (fun A => (ε : ℝ) ≤ |sourceRatio v (k^10) A - 1|) := by
    apply le_trans hgap
    apply matrixProb_mono _ _ _ (sourceP_nonneg _) (le_trans (sourceP_le_half hn) (by norm_num))
    intro A hA
    exact sourceRatio_gap hsourcepos v ε hε A hA
  have hsmall := hN (k^10) (by omega)
  exact (not_lt_of_ge hlow) hsmall

 theorem assemble_full_endpoint (h : FrozenProbabilityEndpoint) : FullFrozenEndpoint := by
  refine ⟨h,source_admissible,?_,sourceMP_tendsto_zero,
    frozen_implies_source_nonconvergence h,frozen_implies_source_ratio_failure h⟩
  intro k hk
  exact ⟨sourceM_agrees k,sourceP_agrees k⟩

end ADG
