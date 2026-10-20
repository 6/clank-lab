import EKG.SmoothedPositions
import EKG.VerifiedSpans

namespace EKG

/-- Finite assembly of the smoothed rate. The inputs are local bounds for
frontiers, upper spans and missing-composite lower spans, not the desired
sequence-rate conclusion. Final verification must instantiate each input. -/
theorem smoothed_error_of_local_bounds (s : GreedySeq) {n : ℕ} (hn : 4 ≤ n)
    {R A B C : ℝ} (hR : 1 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hclock : ∀ k, k ≤ n → n-k ≤ 3 →
      |(frontier s k : ℝ) - ((k+1 : ℕ) : ℝ)| ≤ C*R)
    (hupper : (nonTickTop s n : ℝ) - (frontier s n : ℝ) ≤ A*R)
    (hlower : 1 < s.a n → ¬ (s.a n).Prime →
      (frontier s (n-1) : ℝ) - (s.a n : ℝ) ≤ B*R) :
    |(smoothValue (s.a n) : ℝ) - ((n+1 : ℕ) : ℝ)| ≤ (A+B+C+3)*R := by
  have hAR := mul_nonneg hA (show 0 ≤ R by linarith)
  have hBR := mul_nonneg hB (show 0 ≤ R by linarith)
  have hCR := mul_nonneg hC (show 0 ≤ R by linarith)
  rcases s.smoothed_position_cases hn with hordinary | hfrontier
  · obtain ⟨hbig, hcomp, hnt, hsmooth⟩ := hordinary
    rw [hsmooth]
    have hup := abs_le.mp (hclock n le_rfl (by omega))
    have hlo := abs_le.mp (hclock (n-1) (by omega) (by omega))
    have hr : n-1+1 = n := by omega
    rw [hr] at hlo
    have hlow := hlower hbig hcomp
    have htop : (s.a n : ℝ) ≤ (nonTickTop s n : ℝ) := by
      exact_mod_cast nonTick_le_top s (i := n) le_rfl hnt
    have hsucc : ((n+1 : ℕ) : ℝ) = (n : ℝ)+1 := by simp
    apply abs_le.mpr
    constructor <;> nlinarith
  · have hfront : ∃ k, k ≤ n ∧ n-k ≤ 3 ∧ smoothValue (s.a n) = frontier s k := by
      rcases hfrontier with htwo | hthree
      · exact ⟨n-2, by omega, by omega, htwo⟩
      · exact ⟨n-3, by omega, by omega, hthree⟩
    obtain ⟨k, hkn, hdist, heq⟩ := hfront
    have hc := abs_le.mp (hclock k hkn hdist)
    have hdistNat : n ≤ k+3 := by omega
    have hkn' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hdist' : (n : ℝ) ≤ (k : ℝ)+3 := by exact_mod_cast hdistNat
    rw [heq]
    have hn' : ((n+1 : ℕ) : ℝ) = (n : ℝ)+1 := by simp
    have hk' : ((k+1 : ℕ) : ℝ) = (k : ℝ)+1 := by simp
    rw [hk'] at hc
    apply abs_le.mpr
    constructor <;> nlinarith

/-- Comparing a frontier after a bounded index shift to the final scale.
The slightly wider lower range absorbs the shift without a new limit theorem. -/
theorem logRate_le_of_quarter_comparable {e t : ℝ} (ht : 0 < t)
    (he : t/4 ≤ e) (he' : e ≤ 2*t)
    (hl : 2*Real.log 4 ≤ Real.log t) : logRate e ≤ 4*logRate t := by
  have he0 : 0 < e := by linarith
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlt : 0 < Real.log t := by linarith
  have hle : Real.log t/2 ≤ Real.log e := by
    have h := Real.log_le_log (show 0 < t/4 by positivity) he
    rw [Real.log_div (ne_of_gt ht) (by norm_num)] at h
    linarith
  unfold logRate
  calc
    _ ≤ (2*t)/Real.log e := div_le_div_of_nonneg_right he' (by linarith)
    _ ≤ (2*t)/(Real.log t/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hle
    _ = 4*(t/Real.log t) := by ring

end EKG
