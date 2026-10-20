import EKG.ClockRates
import EKG.CompositePositions
import EKG.RateAssembly

namespace EKG

open Real Filter

/-- The main smoothed rate, for every sequence satisfying the exact EKG rule.
All combinatorial, structural, finite and analytic inputs are proved in the
imported modules; this theorem has no additional mathematical hypotheses. -/
theorem smoothed_rate (s : GreedySeq) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(smoothValue (s.a n) : ℝ) - ((n+1 : ℕ) : ℝ)| ≤
        C * logRate ((n+1 : ℕ) : ℝ) := by
  obtain ⟨C, hC, Nc, hc⟩ := frontier_clock_rate s
  obtain ⟨Nm, hm⟩ := eventually_atTop.mp (eventually_frontier_comparable s)
  obtain ⟨Nu, hu⟩ := eventually_atTop.mp (eventually_nonTickTop_log_span s)
  have hf : Tendsto (fun t => (frontier s t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop s)
  obtain ⟨Nh, hh⟩ := eventually_atTop.mp
    (hf.eventually eventually_positionHoleMajorant_le)
  have htime : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp htime).eventually
      (eventually_ge_atTop (2*Real.log 4)))
  let D : ℝ := 4*793^2+2*793
  refine ⟨4*D+6416+4*C+3, by dsimp [D]; nlinarith,
    Nc+Nm+Nu+Nh+Nl+20, ?_⟩
  intro n hn
  let T : ℝ := ((n+1 : ℕ) : ℝ)
  let R : ℝ := logRate T
  have hn20 : 20 ≤ n := by omega
  have hT1 : 1 < T := by
    dsimp [T]
    exact_mod_cast (show 1 < n+1 by omega)
  have hT : 0 < T := by linarith
  have hlog : 2*Real.log 4 ≤ Real.log T := hl n (by omega)
  have hlog2 : 2*Real.log 2 ≤ Real.log T := by
    have h24 : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    linarith
  have hR : 1 ≤ R := by
    dsimp [R, logRate]
    apply (le_div_iff₀ (Real.log_pos hT1)).mpr
    have h := Real.log_le_sub_one_of_pos hT
    linarith
  have hD : 0 ≤ D := by dsimp [D]; norm_num
  have hnearTime : ∀ k : ℕ, k ≤ n → n-k ≤ 3 →
      T/2 ≤ ((k+1 : ℕ) : ℝ) ∧ ((k+1 : ℕ) : ℝ) ≤ T := by
    intro k hkn hdist
    have hlo : n+1 ≤ 2*(k+1) := by omega
    have hhi : k+1 ≤ n+1 := by omega
    have hlo' : T ≤ 2*((k+1 : ℕ) : ℝ) := by
      dsimp [T]
      exact_mod_cast hlo
    have hhi' : ((k+1 : ℕ) : ℝ) ≤ T := by
      dsimp [T]
      exact_mod_cast hhi
    constructor <;> linarith
  have hnearFrontier : ∀ k : ℕ, k ≤ n → n-k ≤ 3 →
      logRate (frontier s k) ≤ 4*R := by
    intro k hkn hdist
    have hkt := hnearTime k hkn hdist
    have hcomp := hm k (by omega)
    exact logRate_le_of_quarter_comparable hT (by linarith [hcomp.1])
      (by linarith [hcomp.2]) hlog
  have hclock : ∀ k : ℕ, k ≤ n → n-k ≤ 3 →
      |(frontier s k : ℝ) - ((k+1 : ℕ) : ℝ)| ≤ (4*C)*R := by
    intro k hkn hdist
    have hkt := hnearTime k hkn hdist
    have hrate : logRate ((k+1 : ℕ) : ℝ) ≤ 4*R :=
      logRate_le_of_comparable hT hkt.1 (by linarith [hkt.2]) hlog2
    calc
      _ ≤ C*logRate ((k+1 : ℕ) : ℝ) := hc k (by omega)
      _ ≤ C*(4*R) := mul_le_mul_of_nonneg_left hrate hC.le
      _ = (4*C)*R := by ring
  have hupper : (nonTickTop s n : ℝ) - (frontier s n : ℝ) ≤ (4*D)*R := by
    have hup := hu n (by omega)
    have hfront := hnearFrontier n le_rfl (by omega)
    calc
      _ ≤ D*logRate (frontier s n) := hup
      _ ≤ D*(4*R) := mul_le_mul_of_nonneg_left hfront hD
      _ = (4*D)*R := by ring
  have hlower : 1 < s.a n → ¬ (s.a n).Prime →
      (frontier s (n-1) : ℝ) - (s.a n : ℝ) ≤ (6416 : ℝ)*R := by
    intro hbig hnp
    have hfront := hnearFrontier (n-1) (by omega) (by omega)
    calc
      _ ≤ positionHoleMajorant (frontier s (n-1)) :=
        composite_position_lower s (by omega) hbig hnp
      _ ≤ 1604*logRate (frontier s (n-1)) := hh (n-1) (by omega)
      _ ≤ 1604*(4*R) := mul_le_mul_of_nonneg_left hfront (by norm_num)
      _ = 6416*R := by ring
  exact smoothed_error_of_local_bounds s (by omega) hR
    (mul_nonneg (by norm_num) hD) (by norm_num) (mul_nonneg (by norm_num) hC.le)
    hclock hupper hlower

/-- Main target for the canonical EKG sequence, with manuscript index `n+1`.
No prime-pattern, crossing, hole-count or rate hypothesis remains. -/
theorem mainRate : MainRateTarget := by
  obtain ⟨C, hC, N, hN⟩ := smoothed_rate canonical
  refine ⟨C, hC, N, ?_⟩
  intro n hn
  simpa only [canonical, logRate, mul_div_assoc] using hN n hn

end EKG
