import EKG.PartAParameters
import EKG.PartAWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform upper-excursion little-o bound for the literal canonical EKG.
The quantifier order is source constants, delta, fixed M, eta, fixed prime
capacity constant, then observation time and its controlling prime. -/
namespace EKG.PartA

open Real Filter Asymptotics

/-- The complete Part A mathematical endpoint. This declaration still needs
the separately specified dependency-export/kernel acceptance before PASS. -/
theorem canonical_upper_excursion :
    ∀ delta : ℝ, 0 < delta → ∃ u0 : ℕ, ∀ u : ℕ, u0 ≤ u →
      max ((nonTickTop canonical u : ℝ) - (frontier canonical u : ℝ)) 0 ≤
        delta * (frontier canonical u : ℝ) / Real.log (frontier canonical u) := by
  obtain ⟨H, hH, X, hwindow⟩ := window_gap_bound
  intro delta hdelta
  obtain ⟨M, hM, hparameters⟩ := eventually_excursion_parameters delta hdelta
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let eta : ℝ := delta / (32 * H * M)
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨C, hC, hcapacity⟩ := hwindow eta heta
  let R : ℝ := 8 * M * (C + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hf : Tendsto (fun t => (frontier canonical t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop canonical)
  have hsmall : ∀ᶠ e : ℝ in atTop,
      |Real.log e| ≤ (delta / (4 * R)) * Real.sqrt e := by
    have h := (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).bound
      (by positivity : 0 < delta / (4 * R))
    filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with e he he0
    simpa only [Real.norm_eq_abs, ← Real.sqrt_eq_rpow,
      abs_of_nonneg (Real.sqrt_nonneg e)] using he
  have heventual : ∀ᶠ t : ℕ in atTop,
      max ((nonTickTop canonical t : ℝ) - (frontier canonical t : ℝ)) 0 ≤
        delta * logRate (frontier canonical t) := by
    filter_upwards [hparameters, eventually_nonTickTop_log_span canonical,
      hf.eventually (eventually_ge_atTop X),
      hf.eventually (eventually_gt_atTop (3 : ℝ)), hf.eventually hsmall]
      with t hparams hspan hX he3 hlogsmall
    let e : ℝ := frontier canonical t
    let v : ℝ := nonTickTop canonical t
    let B : ℝ := delta / (4 * 793) * Real.sqrt e
    have he : 0 < e := by dsimp [e]; linarith
    have helog : 0 < Real.log e := Real.log_pos (by dsimp [e]; linarith)
    have hL : 0 < logRate e := div_pos he helog
    have hno : ¬ delta * logRate e ≤ v - e := by
      intro hgap
      have p := hparams hgap
      have hlarge : frontier canonical t < nonTickTop canonical t := by
        have := p.gap_large
        omega
      obtain ⟨i, r, hit, hi, hval, hr, hri, hrsq, hrspan⟩ :=
        controlling_prime p.frontier_large p.gap_large
      have hbound := hcapacity t i r M B hX p.frontier_large hlarge
        hi hit hval hr hri hM p.scale_large p.multiplier_lt p.gap_scale
        (p.stride r hrsq hrspan) p.cube (by linarith [hspan]) p.comparable
      have hrsqreal : (r : ℝ)^2 ≤ v := by dsimp [v]; exact_mod_cast hrsq
      have hs : 0 ≤ Real.sqrt e := Real.sqrt_nonneg e
      have hs2 : (Real.sqrt e)^2 = e := Real.sq_sqrt he.le
      have hr0 : (0 : ℝ) ≤ r := by positivity
      have hrbound : (r : ℝ) ≤ 2 * Real.sqrt e := by
        have hv := p.comparable
        change v < 2*e at hv
        nlinarith
      have herr : 4 * (r : ℝ) * M * (C+1) ≤ R * Real.sqrt e := by
        have hm := mul_le_mul_of_nonneg_right hrbound
          (show (0 : ℝ) ≤ 4 * M * (C+1) by positivity)
        dsimp [R]
        nlinarith only [hm]
      have hfirst : 8 * H * eta * (M : ℝ) * logRate e =
          delta / 4 * logRate e := by
        dsimp [eta]
        field_simp [ne_of_gt hH, ne_of_gt hMpos]
        <;> ring
      have hlog : Real.log e ≤ delta / (4*R) * Real.sqrt e :=
        (le_abs_self _).trans hlogsmall
      have hlog' : Real.log e * (4*R) ≤ delta * Real.sqrt e := by
        apply (le_div_iff₀ (show 0 < 4*R by positivity)).mp
        simpa only [div_mul_eq_mul_div] using hlog
      have hlogmul := mul_le_mul_of_nonneg_right hlog' hs
      have herror : R * Real.sqrt e ≤ delta / 4 * logRate e := by
        change R * Real.sqrt e ≤ delta / 4 * (e / Real.log e)
        rw [← mul_div_assoc]
        apply (le_div_iff₀ helog).mpr
        have hdsq : delta * (Real.sqrt e)^2 = delta * e := by rw [hs2]
        nlinarith only [hlogmul, hdsq]
      change v-e ≤ 8*H*eta*(M:ℝ)*logRate e + 4*(r:ℝ)*M*(C+1) at hbound
      rw [hfirst] at hbound
      have hpositive : 0 < delta * logRate e := mul_pos hdelta hL
      linarith
    exact max_le (le_of_lt (lt_of_not_ge hno)) (by positivity)
  obtain ⟨u0, hu0⟩ := eventually_atTop.mp heventual
  refine ⟨u0, ?_⟩
  intro u hu
  simpa only [logRate, ← mul_div_assoc] using hu0 u hu

end EKG.PartA
