import EKG.MainRate

/-!
Uniform adjacent localization from the proved old smoothed rate.
The explicit constant used below is `32 * C + 1`, where `C` is the
fixed witness supplied by `smoothed_rate canonical`.
-/

namespace EKG

open Real Filter

/-- A large ordinary value and its ordinary predecessor are uniformly
close on the logarithmic scale of the value's observation frontier.
The finite prefix maximum first excludes every index before the rate
estimate applies; no inverse clock estimate is assumed.
-/
theorem partA_adjacent_localization :
    ∃ A : ℝ, 0 < A ∧ ∃ X : ℝ, ∀ e : ℝ, X ≤ e → ∀ n : ℕ,
      e < (canonical.a n : ℝ) → (canonical.a n : ℝ) ≤ 2 * e →
      smoothValue (canonical.a n) = canonical.a n →
      smoothValue (canonical.a (n - 1)) = canonical.a (n - 1) →
      |(canonical.a (n - 1) : ℝ) - (canonical.a n : ℝ)| ≤
        A * logRate e := by
  classical
  obtain ⟨C, hC, N₀, hN₀⟩ := smoothed_rate canonical
  have htime : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  obtain ⟨Nlog, hNlog⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp htime).eventually
      (eventually_ge_atTop (2 * C)))
  let N : ℕ := N₀ + Nlog + 2
  let F : ℕ := (Finset.range N).sup canonical.a
  refine ⟨32 * C + 1, by positivity,
    max 6 (max (F : ℝ) (Real.exp (2 * Real.log 4))), ?_⟩
  intro e he n hey hyupper hysmooth hdsmooth
  have he6 : 6 ≤ e := (le_max_left _ _).trans he
  have heinner : max (F : ℝ) (Real.exp (2 * Real.log 4)) ≤ e :=
    (le_max_right _ _).trans he
  have heF : (F : ℝ) ≤ e := (le_max_left _ _).trans heinner
  have heexp : Real.exp (2 * Real.log 4) ≤ e :=
    (le_max_right _ _).trans heinner
  have hepos : 0 < e := by linarith
  have heone : 1 < e := by linarith
  have hnN : N ≤ n := by
    by_contra h
    have hnsmall : n < N := by omega
    have hbound : canonical.a n ≤ F :=
      Finset.le_sup (Finset.mem_range.mpr hnsmall)
    have hboundreal : (canonical.a n : ℝ) ≤ (F : ℝ) := by
      exact_mod_cast hbound
    linarith
  have hnbase : N₀ ≤ n := by dsimp [N] at hnN; omega
  have hnprevbase : N₀ ≤ n - 1 := by dsimp [N] at hnN; omega
  have hnlog : Nlog ≤ n := by dsimp [N] at hnN; omega
  have hntwo : 2 ≤ n := by dsimp [N] at hnN; omega
  let T : ℝ := ((n + 1 : ℕ) : ℝ)
  have hTreal : T = (n : ℝ) + 1 := by simp [T]
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hlogTlarge : 2 * C ≤ Real.log T := hNlog n hnlog
  have hlogTpos : 0 < Real.log T := by linarith
  have hcurrent := hN₀ n hnbase
  rw [hysmooth] at hcurrent
  change |(canonical.a n : ℝ) - T| ≤ C * logRate T at hcurrent
  have hhalf : C * logRate T ≤ T / 2 := by
    unfold logRate
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hlogTpos).mpr
    have hmul := mul_le_mul_of_nonneg_left hlogTlarge hTpos.le
    nlinarith only [hmul]
  have hcurrenthalf := abs_le.mp (hcurrent.trans hhalf)
  have hTlower : e / 2 ≤ T := by linarith [hcurrenthalf.2]
  have hTupper : T ≤ 4 * e := by linarith [hcurrenthalf.1]
  have hnlower : e / 2 ≤ (n : ℝ) := by
    linarith [hcurrenthalf.2]
  have hnupper : (n : ℝ) ≤ 4 * e := by linarith
  have hlogE : 2 * Real.log 4 ≤ Real.log e := by
    have h := Real.log_le_log (Real.exp_pos (2 * Real.log 4)) heexp
    rwa [Real.log_exp] at h
  have hlog24 : Real.log 2 ≤ Real.log 4 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlogE2 : 2 * Real.log 2 ≤ Real.log e := by linarith
  have hlogDouble : 2 * Real.log 4 ≤ Real.log (2 * e) :=
    hlogE.trans (Real.log_le_log hepos (by linarith))
  have hdouble : logRate (2 * e) ≤ 4 * logRate e :=
    logRate_le_of_comparable hepos (by linarith) (by linarith) hlogE2
  have hrate : ∀ x : ℝ, e / 2 ≤ x → x ≤ 4 * e →
      logRate x ≤ 16 * logRate e := by
    intro x hxlower hxupper
    have hx := logRate_le_of_quarter_comparable
      (show 0 < 2 * e by linarith) (by linarith : (2 * e) / 4 ≤ x)
      (by linarith : x ≤ 2 * (2 * e)) hlogDouble
    calc
      logRate x ≤ 4 * logRate (2 * e) := hx
      _ ≤ 4 * (4 * logRate e) :=
        mul_le_mul_of_nonneg_left hdouble (by norm_num)
      _ = 16 * logRate e := by ring
  have hrateone : 1 ≤ logRate e := by
    unfold logRate
    apply (le_div_iff₀ (Real.log_pos heone)).mpr
    have h := Real.log_le_sub_one_of_pos hepos
    linarith
  have hprevious := hN₀ (n - 1) hnprevbase
  rw [hdsmooth, show n - 1 + 1 = n by omega] at hprevious
  have hcurrentbound : |(canonical.a n : ℝ) - T| ≤
      C * (16 * logRate e) :=
    hcurrent.trans (mul_le_mul_of_nonneg_left (hrate T hTlower hTupper) hC.le)
  have hpreviousbound : |(canonical.a (n - 1) : ℝ) - (n : ℝ)| ≤
      C * (16 * logRate e) :=
    hprevious.trans
      (mul_le_mul_of_nonneg_left (hrate (n : ℝ) hnlower hnupper) hC.le)
  have hunit : |(n : ℝ) - T| = 1 := by
    have h : (n : ℝ) - T = -1 := by linarith
    rw [h]
    norm_num
  have htriangle := abs_sub_le (canonical.a (n - 1) : ℝ) (n : ℝ)
    (canonical.a n : ℝ)
  have htriangle' := abs_sub_le (n : ℝ) T (canonical.a n : ℝ)
  rw [hunit, abs_sub_comm T (canonical.a n : ℝ)] at htriangle'
  nlinarith only [htriangle, htriangle', hcurrentbound, hpreviousbound, hrateone]

end EKG
