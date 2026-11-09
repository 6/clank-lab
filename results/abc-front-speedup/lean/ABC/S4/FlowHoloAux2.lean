import Mathlib

/-! L0a helper: the radial retraction onto a closed ball is 2-Lipschitz. -/

open Set Metric Filter Topology

noncomputable section

namespace ABC.S4.FlowHoloAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial retraction of `E` onto `closedBall 0 ε`. -/
def clampR (ε : ℝ) (v : E) : E := if ‖v‖ ≤ ε then v else (ε / ‖v‖) • v

theorem clampR_of_le {ε : ℝ} {v : E} (h : ‖v‖ ≤ ε) : clampR ε v = v := by simp [clampR, h]

theorem norm_clampR_le {ε : ℝ} (hε : 0 ≤ ε) (v : E) : ‖clampR ε v‖ ≤ ε := by
  unfold clampR
  split_ifs with h
  · exact h
  · push Not at h
    have hv : 0 < ‖v‖ := hε.trans_lt h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hε hv.le)]
    field_simp
    exact le_rfl

private theorem aux_out_in {ε : ℝ} {v w : E} (hv : ε < ‖v‖) (hw : ‖w‖ ≤ ε) :
    ‖(ε / ‖v‖) • v - w‖ ≤ 2 * ‖v - w‖ := by
  have hnv : 0 < ‖v‖ := lt_of_le_of_lt (norm_nonneg w) (hw.trans_lt hv)
  have h1 : ‖(ε / ‖v‖) • v - v‖ = ‖v‖ - ε := by
    have : (ε / ‖v‖) • v - v = (ε / ‖v‖ - 1) • v := by rw [sub_smul, one_smul]
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonpos]
    · field_simp; ring
    · rw [sub_nonpos, div_le_one hnv]; exact hv.le
  have h2 : ‖v‖ - ‖w‖ ≤ ‖v - w‖ := norm_sub_norm_le v w
  calc ‖(ε / ‖v‖) • v - w‖ = ‖((ε / ‖v‖) • v - v) + (v - w)‖ := by congr 1; abel
    _ ≤ ‖(ε / ‖v‖) • v - v‖ + ‖v - w‖ := norm_add_le _ _
    _ ≤ 2 * ‖v - w‖ := by rw [h1]; linarith

private theorem aux_out_out {ε : ℝ} (hε : 0 < ε) {v w : E} (hw : ε < ‖w‖) (hvw : ‖w‖ ≤ ‖v‖) :
    ‖(ε / ‖v‖) • v - (ε / ‖w‖) • w‖ ≤ 2 * ‖v - w‖ := by
  have hnw : 0 < ‖w‖ := hε.trans hw
  have hnv : 0 < ‖v‖ := hnw.trans_le hvw
  set a := ε / ‖v‖
  set b := ε / ‖w‖
  have hb1 : b ≤ 1 := by rw [div_le_one hnw]; exact hw.le
  have hb0 : 0 ≤ b := by positivity
  have hab : a ≤ b := div_le_div_of_nonneg_left hε.le hnw hvw
  have h2 : ‖v‖ - ‖w‖ ≤ ‖v - w‖ := norm_sub_norm_le v w
  have h3 : (b - a) * ‖v‖ ≤ ‖v‖ - ‖w‖ := by
    have : (b - a) * ‖v‖ = ε * (‖v‖ - ‖w‖) / ‖w‖ := by
      simp only [a, b]; field_simp
    rw [this, div_le_iff₀ hnw]
    nlinarith
  calc ‖a • v - b • w‖ = ‖b • (v - w) - (b - a) • v‖ := by
        congr 1; rw [smul_sub, sub_smul]; abel
    _ ≤ ‖b • (v - w)‖ + ‖(b - a) • v‖ := norm_sub_le _ _
    _ = b * ‖v - w‖ + (b - a) * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb0,
          abs_of_nonneg (sub_nonneg.mpr hab)]
    _ ≤ 1 * ‖v - w‖ + (‖v‖ - ‖w‖) := by gcongr
    _ ≤ 2 * ‖v - w‖ := by linarith

theorem lipschitzWith_clampR {ε : ℝ} (hε : 0 < ε) : LipschitzWith 2 (clampR ε : E → E) := by
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  unfold clampR
  split_ifs with hv hw hw
  · linarith [norm_nonneg (v - w)]
  · push Not at hw
    rw [norm_sub_rev, norm_sub_rev v]
    exact aux_out_in hw hv
  · push Not at hv
    exact aux_out_in hv hw
  · push Not at hv hw
    rcases le_total ‖w‖ ‖v‖ with h | h
    · exact aux_out_out hε hw h
    · rw [norm_sub_rev, norm_sub_rev v]
      exact aux_out_out hε hv h

end ABC.S4.FlowHoloAux
