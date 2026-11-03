import DeterministicExchange

/-! From isolated bad paths to the additive and relative Greedy/LP gap. -/
namespace ADG
open Finset

lemma selected_exchange_mass {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A) :
    3 * (tripleCount A + B A) ≤ m := by
  classical
  have hc : ((exchangedTriples A).biUnion A).card = 3 * (exchangedTriples A).card := by
    rw [Finset.card_biUnion (by
      intro j hj k hk hne
      exact exchangedTriples_support_disjoint A hn j hj k hk hne)]
    calc
      (∑ j ∈ exchangedTriples A, (A j).card) = ∑ _j ∈ exchangedTriples A, 3 :=
        Finset.sum_congr rfl (exchangedTriples_support_card A hn)
      _ = 3 * (exchangedTriples A).card := by simp [Nat.mul_comm]
  have hle := Finset.card_le_card (Finset.subset_univ ((exchangedTriples A).biUnion A))
  simpa [hc, exchangedTriples_card A hn] using hle

lemma actual_greedy_count {m n : ℕ} (A : Matrix m n) (hm : 2 ≤ m)
    (hn : noLargeColumns A) (hp : allExactPairs A) :
    G A = (m-tripleCount A+1)/2 := by
  obtain ⟨K,T,hK,hphase,hnd,hd,hG⟩ := greedy_phase_count m n A hm hn hp
  simpa [hK] using hG

/-- Every actual isolated bad middle gives half a unit of additive saving,
up to one global half-unit of rounding. -/
theorem actual_greedy_lp_additive_gap {m n : ℕ} (A : Matrix m n) (hm : 2 ≤ m)
    (hn : noLargeColumns A) (hp : allExactPairs A) :
    ((B A : ℝ)-1)/2 ≤ (G A : ℝ)-L A := by
  have hmass := selected_exchange_mass A hn
  have hG := actual_greedy_count A hm hn hp
  have hL := lp_le_isolated_path_exchange A hm hn hp
  have hnat : m-tripleCount A-B A+1 ≤ 2*((m-tripleCount A-B A+1)/2)+1 := by omega
  have hnat' : 2*((m-tripleCount A-B A+1)/2) ≤ m-tripleCount A-B A+1 := by omega
  have hGnat : m-tripleCount A ≤ 2*G A := by omega
  have hK : tripleCount A ≤ m := by omega
  have hKB : tripleCount A+B A ≤ m := by omega
  have hcast : ((m-tripleCount A-B A+1 : ℕ) : ℝ) =
      (m : ℝ)-(tripleCount A : ℝ)-(B A : ℝ)+1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_sub hK]
    norm_num
  have hcast' : ((m-tripleCount A : ℕ) : ℝ) = (m : ℝ)-(tripleCount A : ℝ) := by
    exact Nat.cast_sub hK
  have hgreal : (m : ℝ)-(tripleCount A : ℝ) ≤ 2*(G A : ℝ) := by
    simpa [hcast'] using (show ((m-tripleCount A : ℕ) : ℝ) ≤ (2*G A : ℕ) by exact_mod_cast hGnat)
  have hlreal : 2*(((m-tripleCount A-B A+1)/2 : ℕ) : ℝ) ≤
      (m : ℝ)-(tripleCount A : ℝ)-(B A : ℝ)+1 := by
    simpa [hcast] using (show ((2*((m-tripleCount A-B A+1)/2) : ℕ) : ℝ) ≤
      ((m-tripleCount A-B A+1 : ℕ) : ℝ) by exact_mod_cast hnat')
  linarith

lemma actual_lp_le_rows {m n : ℕ} (A : Matrix m n) (hm : 2 ≤ m)
    (hn : noLargeColumns A) (hp : allExactPairs A) : L A ≤ (m : ℝ) := by
  have hL := lp_le_isolated_path_exchange A hm hn hp
  have hc : (m-tripleCount A-B A+1)/2 ≤ m := by omega
  exact hL.trans (by exact_mod_cast hc)

/-- Generic positive-density transport, on actual matrices. -/
theorem actual_greedy_lp_gap_of_bad_density {m n : ℕ} (A : Matrix m n) (hm : 2 ≤ m)
    (hn : noLargeColumns A) (hp : allExactPairs A)
    (α : ℝ) (hα : 0 ≤ α) (hB : α*(m : ℝ) ≤ (B A : ℝ))
    (hlarge : 2 ≤ α*(m : ℝ)) :
    (1+α/4)*L A ≤ (G A : ℝ) := by
  have hadd := actual_greedy_lp_additive_gap A hm hn hp
  have hL := actual_lp_le_rows A hm hn hp
  have hmul : α*L A ≤ α*(m : ℝ) := mul_le_mul_of_nonneg_left hL hα
  linarith

end ADG
