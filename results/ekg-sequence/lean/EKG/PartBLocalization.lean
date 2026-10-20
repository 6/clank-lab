import EKG.MainRate
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
Uniform occurrence cutoffs and successor localization for canonical EKG.
Only a finite prefix maximum and the old smoothed rate are used. The
localization constant is `32 * C + 1`, for the fixed positive constant
`C` supplied by `smoothed_rate canonical`; it is independent of the
requested occurrence-index cutoff.
-/

namespace EKG.PartB

open Real Filter

/-- A large raw value cannot occur in a prescribed finite prefix. This
cutoff does not require any smoothing or successor information.
-/
theorem occurrence_late (N : ℕ) :
    ∃ X : ℝ, ∀ e : ℝ, X ≤ e → ∀ i : ℕ,
      e / 2 < (canonical.a i : ℝ) → N ≤ i := by
  classical
  let F : ℕ := (Finset.range N).sup canonical.a
  refine ⟨2 * (F : ℝ), ?_⟩
  intro e he i hy
  by_contra h
  have hi : i < N := by omega
  have hbound : canonical.a i ≤ F :=
    Finset.le_sup (Finset.mem_range.mpr hi)
  have hboundreal : (canonical.a i : ℝ) ≤ (F : ℝ) := by
    exact_mod_cast hbound
  linarith

/-- Monotonicity of `x / log x` on the range where `log x ≥ 1`.
This elementary comparison permits a post-occurrence frontier to be
smaller than the final frontier without replacing it by the latter.
-/
theorem logRate_mono_of_one_le_log {f e : ℝ}
    (hf : 0 < f) (hlogf : 1 ≤ Real.log f) (hfe : f ≤ e) :
    logRate f ≤ logRate e := by
  have he : 0 < e := hf.trans_le hfe
  have hlogfpos : 0 < Real.log f := by linarith
  have hloge : 0 < Real.log e :=
    hlogfpos.trans_le (Real.log_le_log hf hfe)
  have hexpf : Real.exp 1 ≤ f := (Real.le_log_iff_exp_le hf).mp hlogf
  have hratio := Real.log_div_self_antitoneOn hexpf (hexpf.trans hfe) hfe
  have hcross := (div_le_div_iff₀ he hf).mp hratio
  unfold logRate
  apply (div_le_div_iff₀ hlogfpos hloge).mpr
  nlinarith only [hcross]

/-- Every sufficiently large ordinary occurrence has both an arbitrarily
late index and an ordinary successor within one fixed logarithmic window.
The constant precedes the requested index cutoff; the value threshold
follows that cutoff and works uniformly at every qualifying occurrence.
-/
theorem successor_localization :
    ∃ H : ℝ, 0 < H ∧ ∀ N : ℕ, ∃ X : ℝ,
      ∀ e : ℝ, X ≤ e → ∀ i : ℕ,
        e / 2 < (canonical.a i : ℝ) → (canonical.a i : ℝ) ≤ e →
        smoothValue (canonical.a i) = canonical.a i →
        smoothValue (canonical.a (i + 1)) = canonical.a (i + 1) →
        N ≤ i ∧
          |(canonical.a (i + 1) : ℝ) - (canonical.a i : ℝ)| ≤
            H * logRate e := by
  classical
  obtain ⟨C, hC, N₀, hN₀⟩ := smoothed_rate canonical
  have htime : Tendsto (fun i : ℕ => ((i + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  obtain ⟨Nlog, hNlog⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp htime).eventually
      (eventually_ge_atTop (max (2 * C) (2 * Real.log 2))))
  refine ⟨32 * C + 1, by positivity, ?_⟩
  intro N
  obtain ⟨Xocc, hocc⟩ := occurrence_late (N + N₀ + Nlog + 2)
  refine ⟨max 6 (max Xocc (Real.exp (2 * Real.log 4))), ?_⟩
  intro e he i hy hyupper hysmooth husmooth
  have he6 : 6 ≤ e := (le_max_left _ _).trans he
  have heinner : max Xocc (Real.exp (2 * Real.log 4)) ≤ e :=
    (le_max_right _ _).trans he
  have heocc : Xocc ≤ e := (le_max_left _ _).trans heinner
  have heexp : Real.exp (2 * Real.log 4) ≤ e :=
    (le_max_right _ _).trans heinner
  have hepos : 0 < e := by linarith
  have heone : 1 < e := by linarith
  have hi : N + N₀ + Nlog + 2 ≤ i := hocc e heocc i hy
  have hiN : N ≤ i := by omega
  have hibase : N₀ ≤ i := by omega
  have hinextbase : N₀ ≤ i + 1 := by omega
  have hilog : Nlog ≤ i := by omega
  let T : ℝ := ((i + 1 : ℕ) : ℝ)
  let U : ℝ := ((i + 1 + 1 : ℕ) : ℝ)
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hTone : 1 ≤ T := by
    dsimp [T]
    exact_mod_cast (show 1 ≤ i + 1 by omega)
  have hUT : U = T + 1 := by simp [T, U]
  have hlogTbound : max (2 * C) (2 * Real.log 2) ≤ Real.log T := hNlog i hilog
  have hlogTlarge : 2 * C ≤ Real.log T :=
    (le_max_left _ _).trans hlogTbound
  have hlogTtwo : 2 * Real.log 2 ≤ Real.log T :=
    (le_max_right _ _).trans hlogTbound
  have hlogTpos : 0 < Real.log T := by linarith
  have hcurrent := hN₀ i hibase
  rw [hysmooth] at hcurrent
  change |(canonical.a i : ℝ) - T| ≤ C * logRate T at hcurrent
  have hhalf : C * logRate T ≤ T / 2 := by
    unfold logRate
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hlogTpos).mpr
    have hmul := mul_le_mul_of_nonneg_left hlogTlarge hTpos.le
    nlinarith only [hmul]
  have hcurrenthalf := abs_le.mp (hcurrent.trans hhalf)
  have hTlower : e / 4 ≤ T := by linarith [hcurrenthalf.2]
  have hTupper : T ≤ 2 * e := by linarith [hcurrenthalf.1]
  have hlogE : 2 * Real.log 4 ≤ Real.log e := by
    have h := Real.log_le_log (Real.exp_pos (2 * Real.log 4)) heexp
    rwa [Real.log_exp] at h
  have hL : 0 ≤ logRate e := logRate_nonneg heone
  have hrateTfour : logRate T ≤ 4 * logRate e :=
    logRate_le_of_quarter_comparable hepos hTlower hTupper hlogE
  have hrateT : logRate T ≤ 16 * logRate e := by linarith
  have hrateUT : logRate U ≤ 4 * logRate T :=
    logRate_le_of_comparable hTpos (by linarith) (by linarith) hlogTtwo
  have hrateU : logRate U ≤ 16 * logRate e := by linarith
  have hrateone : 1 ≤ logRate e := by
    unfold logRate
    apply (le_div_iff₀ (Real.log_pos heone)).mpr
    have h := Real.log_le_sub_one_of_pos hepos
    linarith
  have hnext := hN₀ (i + 1) hinextbase
  rw [husmooth] at hnext
  change |(canonical.a (i + 1) : ℝ) - U| ≤ C * logRate U at hnext
  have hcurrentbound : |(canonical.a i : ℝ) - T| ≤ C * (16 * logRate e) :=
    hcurrent.trans (mul_le_mul_of_nonneg_left hrateT hC.le)
  have hnextbound : |(canonical.a (i + 1) : ℝ) - U| ≤ C * (16 * logRate e) :=
    hnext.trans (mul_le_mul_of_nonneg_left hrateU hC.le)
  have hunit : |U - T| = 1 := by
    have h : U - T = 1 := by linarith
    rw [h]
    norm_num
  have htriangle := abs_sub_le (canonical.a (i + 1) : ℝ) U (canonical.a i : ℝ)
  have htriangle' := abs_sub_le U T (canonical.a i : ℝ)
  rw [hunit, abs_sub_comm T (canonical.a i : ℝ)] at htriangle'
  refine ⟨hiN, ?_⟩
  nlinarith only [htriangle, htriangle', hcurrentbound, hnextbound, hrateone]

end EKG.PartB
