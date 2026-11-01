import FT23.GeneratorConvex
import Mathlib.Order.Filter.AtTopBot.Field

noncomputable section
open Set Filter
open scoped Topology
namespace FT23

lemma phi_strictAnti_positive : StrictAntiOn phi (Ioc (0:ℝ) 1) := by
  intro u hu v hv huv
  have hl : Real.log u < Real.log v := Real.log_lt_log hu.1 huv
  unfold phi
  apply max_lt_iff.mpr
  constructor
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

lemma psi_strictAnti_all : StrictAnti psi := by
  intro s t hst
  rw [psi_exp_max, psi_exp_max]
  apply Real.exp_lt_exp.mpr
  apply max_lt_iff.mpr
  constructor
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

lemma phi_nonnegative {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) : 0 ≤ phi u := by
  exact le_trans (neg_nonneg.mpr (Real.log_nonpos hu.1.le hu.2)) (le_max_left _ _)

lemma phi_continuous_positive : ContinuousOn phi (Ioc (0:ℝ) 1) := by
  have hl : ContinuousOn Real.log (Ioc (0:ℝ) 1) := by
    intro u hu
    exact (Real.continuousAt_log hu.1.ne').continuousWithinAt
  have hsecond : ContinuousOn (fun u : ℝ => -2*Real.log u-Real.log 16) (Ioc (0:ℝ) 1) :=
    (continuousOn_const.mul hl).sub continuousOn_const
  exact hl.neg.sup hsecond

lemma psi_continuous_all : Continuous psi := by
  unfold psi
  fun_prop

lemma phi_tends_infinity : Tendsto phi (𝓝[>] 0) atTop := by
  have hn : Tendsto (fun u : ℝ => -Real.log u) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  exact tendsto_atTop_mono (fun u => le_max_left (-Real.log u) _) hn

lemma psi_tends_zero : Tendsto psi atTop (𝓝 0) := by
  have hh : Tendsto (fun t : ℝ => t/2) atTop atTop :=
    (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).atTop_div_const (by norm_num)
  have he : Tendsto (fun t : ℝ => Real.exp (-t/2)) atTop (𝓝 0) := by
    simpa only [neg_div] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hh
  have hd : Tendsto (fun t : ℝ => Real.exp (-t/2)/4) atTop (𝓝 0) := by
    simpa using he.div_const 4
  simpa only [psi, max_self] using Real.tendsto_exp_neg_atTop_nhds_zero.max hd

theorem exact_generator : StrictGenerator phi psi := by
  refine ⟨?_, phi_continuous_positive, phi_strictAnti_positive, phi_convex_positive,
    phi_one, phi_tends_infinity, psi_continuous_all.continuousOn,
    psi_strictAnti_all.strictAntiOn _, ?_, ?_, psi_zero, psi_tends_zero, ?_, ?_⟩
  · exact fun u hu => phi_nonnegative hu
  · exact psi_convex_univ.subset (subset_univ _) (convex_Ici (0:ℝ))
  · exact fun t ht => psi_positive t
  · exact fun u hu => psi_phi_positive hu.1
  · exact fun t ht => phi_psi_all t

end FT23
