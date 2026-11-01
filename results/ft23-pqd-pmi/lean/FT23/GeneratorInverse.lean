import FT23.Definitions

/- Exact generator inverse identities. -/
noncomputable section
namespace FT23

lemma log_sixteen : Real.log 16 = 2 * Real.log 4 := by
  rw [show (16:ℝ) = 4*4 by norm_num,
    Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0)]
  ring

lemma psi_exp_max (t : ℝ) :
    psi t = Real.exp (max (-t) (-t/2 - Real.log 4)) := by
  have he : Real.exp (-t/2 - Real.log 4) = Real.exp (-t/2) / 4 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 4)]
  unfold psi
  rw [← he]
  rcases le_total (-t) (-t/2 - Real.log 4) with h | h
  · rw [max_eq_right h, max_eq_right (Real.exp_le_exp.mpr h)]
  · rw [max_eq_left h, max_eq_left (Real.exp_le_exp.mpr h)]

lemma log_psi (t : ℝ) :
    Real.log (psi t) = max (-t) (-t/2 - Real.log 4) := by
  rw [psi_exp_max, Real.log_exp]

lemma inverse_max_forward (x L : ℝ) :
    max (-(max x (2*x-2*L))) (-(max x (2*x-2*L))/2-L) = -x := by
  by_cases h : x ≤ 2*L
  · rw [max_eq_left (by linarith : 2*x-2*L ≤ x)]
    exact max_eq_left (by linarith)
  · rw [max_eq_right (by linarith : x ≤ 2*x-2*L)]
    rw [max_eq_right (by linarith : -(2*x-2*L) ≤ -(2*x-2*L)/2-L)]
    ring

lemma inverse_max_reverse (t L : ℝ) :
    max (-(max (-t) (-t/2-L))) (-2*max (-t) (-t/2-L)-2*L) = t := by
  by_cases h : t ≤ 2*L
  · rw [max_eq_left (by linarith : -t/2-L ≤ -t)]
    rw [max_eq_left (by linarith : -2*(-t)-2*L ≤ -(-t))]
    ring
  · rw [max_eq_right (by linarith : -t ≤ -t/2-L)]
    rw [max_eq_right (by linarith : -(-t/2-L) ≤ -2*(-t/2-L)-2*L)]
    ring

lemma psi_phi_positive {u : ℝ} (hu : 0 < u) : psi (phi u) = u := by
  have hphi : phi u = max (-Real.log u) (2*(-Real.log u)-2*Real.log 4) := by
    unfold phi
    rw [log_sixteen]
    congr 1
    ring
  have hi : max (-(phi u)) (-(phi u)/2 - Real.log 4) = Real.log u := by
    rw [hphi]
    simpa only [neg_neg] using inverse_max_forward (-Real.log u) (Real.log 4)
  rw [psi_exp_max, hi, Real.exp_log hu]

lemma phi_psi_all (t : ℝ) : phi (psi t) = t := by
  unfold phi
  rw [log_psi, log_sixteen]
  exact inverse_max_reverse t (Real.log 4)

lemma psi_positive (t : ℝ) : 0 < psi t := by
  rw [psi_exp_max]
  exact Real.exp_pos _

lemma psi_antitone : Antitone psi := by
  intro s t hst
  rw [psi_exp_max, psi_exp_max]
  apply Real.exp_le_exp.mpr
  exact max_le_max (by linarith) (by linarith)

lemma phi_antitone : AntitoneOn phi (Set.Ioc (0:ℝ) 1) := by
  intro u hu v hv huv
  have hl : Real.log u ≤ Real.log v := Real.log_le_log hu.1 huv
  unfold phi
  exact max_le_max (by linarith) (by linarith)

lemma phi_one : phi 1 = 0 := by
  norm_num [phi]
  exact Real.log_nonneg (by norm_num)
lemma psi_zero : psi 0 = 1 := by norm_num [psi]

end FT23
