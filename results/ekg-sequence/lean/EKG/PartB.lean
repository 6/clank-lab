import EKG.PartBParameters
import EKG.PartBWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Strict uniform late-composite bound for the actual canonical EKG.
The single index threshold precedes both the observation time and hole.
Part A is imported as its proved canonical theorem through the injection.
-/
namespace EKG.PartB

open Real Filter Asymptotics

theorem canonical_missing_composite :
    ∀ delta : ℝ, 0 < delta → ∃ u0 : ℕ, ∀ u : ℕ, u0 ≤ u →
      ∀ h : ℕ, 2 ≤ h → ¬ h.Prime → h < frontier canonical u →
        ¬ UsedBefore canonical.a (u+1) h →
        (frontier canonical u : ℝ)-(h : ℝ) <
          delta*(frontier canonical u : ℝ)/Real.log (frontier canonical u) := by
  obtain ⟨H,hH,hwindow⟩ := window_gap_bound
  intro delta hdelta
  obtain ⟨M,hM,hparameters⟩ := eventually_hole_parameters delta hdelta
  obtain ⟨X,hwin⟩ := hwindow delta hdelta
  have hMpos : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  let eta : ℝ := delta/(16*H*M)
  have heta : 0<eta := by dsimp [eta]; positivity
  obtain ⟨C,hC,hcapacity⟩ := hwin eta heta
  let R : ℝ := 4*M*(C+2)
  have hR : 0<R := by dsimp [R]; positivity
  have hf : Tendsto (fun t => (frontier canonical t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop canonical)
  have hsmall : ∀ᶠ e : ℝ in atTop,
      |Real.log e| ≤ (delta/(4*R))*Real.sqrt e := by
    have h := (isLittleO_log_rpow_atTop (r:=(1/2:ℝ)) (by norm_num)).bound
      (by positivity : 0<delta/(4*R))
    filter_upwards [h,eventually_gt_atTop (0:ℝ)] with e he he0
    simpa only [Real.norm_eq_abs,←Real.sqrt_eq_rpow,
      abs_of_nonneg (Real.sqrt_nonneg e)] using he
  have heventual : ∀ᶠ t : ℕ in atTop, ∀ h : ℕ,
      2 ≤ h → ¬ h.Prime → h < frontier canonical t →
      ¬ UsedBefore canonical.a (t+1) h →
      (frontier canonical t : ℝ)-(h : ℝ) < delta*logRate (frontier canonical t) := by
    filter_upwards [hparameters,hf.eventually (eventually_ge_atTop X),
      hf.eventually (eventually_gt_atTop (3:ℝ)),hf.eventually hsmall]
      with t hparams hX he3 hlogsmall
    intro h hh hnp hbelow hfree
    let e : ℝ := frontier canonical t
    let B : ℝ := delta/(6*802)*Real.sqrt e
    have he : 0<e := by dsimp [e]; linarith
    have helog : 0<Real.log e := Real.log_pos (by dsimp [e]; linarith)
    have hL : 0<logRate e := div_pos he helog
    by_contra hno
    have hgap : delta*logRate e ≤ e-(h : ℝ) := le_of_not_gt hno
    have p := hparams h hh hnp hbelow hfree hgap
    have hbound := hcapacity t h h.minFac M B hX hh hbelow hfree
      p.factor_prime p.factor_dvd hM p.scale_large p.multiplier_lt hgap
      p.gap_upper p.rough_scale p.stride p.cube
    have hssq : (h.minFac : ℝ)^2 ≤ (h : ℝ) := by exact_mod_cast p.factor_sq
    have hhe : (h : ℝ) ≤ e := by dsimp [e]; exact_mod_cast hbelow.le
    have hs0 : (0:ℝ) ≤ h.minFac := by positivity
    have hroot0 : 0 ≤ Real.sqrt e := Real.sqrt_nonneg e
    have hroot2 : (Real.sqrt e)^2=e := Real.sq_sqrt he.le
    have hsbound : (h.minFac : ℝ) ≤ Real.sqrt e := by nlinarith
    have herr : 4*(h.minFac : ℝ)*M*(C+2) ≤ R*Real.sqrt e := by
      have hm := mul_le_mul_of_nonneg_right hsbound
        (show (0:ℝ) ≤ 4*M*(C+2) by positivity)
      dsimp [R]
      nlinarith only [hm]
    have hfirst : 4*H*eta*(M : ℝ)*logRate e=delta/4*logRate e := by
      dsimp [eta]
      field_simp [ne_of_gt hH,ne_of_gt hMpos]
      <;> ring
    have hlog : Real.log e ≤ delta/(4*R)*Real.sqrt e :=
      (le_abs_self _).trans hlogsmall
    have hlog' : Real.log e*(4*R) ≤ delta*Real.sqrt e := by
      apply (le_div_iff₀ (show 0<4*R by positivity)).mp
      simpa only [div_mul_eq_mul_div] using hlog
    have hlogmul := mul_le_mul_of_nonneg_right hlog' hroot0
    have herror : R*Real.sqrt e ≤ delta/4*logRate e := by
      change R*Real.sqrt e ≤ delta/4*(e/Real.log e)
      rw [←mul_div_assoc]
      apply (le_div_iff₀ helog).mpr
      have hdsq : delta*(Real.sqrt e)^2=delta*e := by rw [hroot2]
      nlinarith only [hlogmul,hdsq]
    change e-(h : ℝ) ≤ 4*H*eta*(M : ℝ)*logRate e+
      4*(h.minFac : ℝ)*M*(C+2) at hbound
    rw [hfirst] at hbound
    have hpositive : 0<delta*logRate e := mul_pos hdelta hL
    linarith
  obtain ⟨u0,hu0⟩ := eventually_atTop.mp heventual
  refine ⟨u0,?_⟩
  intro u hu h hh hnp hbelow hfree
  simpa only [logRate,←mul_div_assoc] using hu0 u hu h hh hnp hbelow hfree

end EKG.PartB
