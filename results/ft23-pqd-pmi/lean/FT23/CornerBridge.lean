import FT23.GeneratorInverse

noncomputable section
namespace FT23

lemma phi_high {u : ℝ} (hu : (1:ℝ)/16 ≤ u) : phi u = -Real.log u := by
  have hp : 0 < u := by linarith
  have hlog : 0 ≤ Real.log (16*u) := Real.log_nonneg (by linarith)
  rw [Real.log_mul (by norm_num : (16:ℝ) ≠ 0) hp.ne'] at hlog
  exact max_eq_left (by linarith)

/-- This theorem connects the rational finite interfaces to the ORIGINAL generator. -/
theorem C_high_branch {u v : ℝ} (hu : (1:ℝ)/16 ≤ u) (hv : (1:ℝ)/16 ≤ v) :
    C u v = max (u*v) (Real.sqrt (u*v)/4) := by
  have hu' : 0 < u := by linarith
  have hv' : 0 < v := by linarith
  let s := Real.log u + Real.log v
  have hp : Real.exp s = u*v := by
    dsimp [s]
    rw [Real.exp_add, Real.exp_log hu', Real.exp_log hv']
  have hs : (Real.exp (s/2))^2 = u*v := by
    calc
      _ = Real.exp (s/2+s/2) := by rw [pow_two, Real.exp_add]
      _ = Real.exp s := by congr 1; ring
      _ = u*v := hp
  have hroot : Real.exp (s/2) = Real.sqrt (u*v) := by
    exact ((Real.sqrt_eq_iff_eq_sq (mul_pos hu' hv').le (Real.exp_pos _).le).mpr hs.symm).symm
  rw [C, if_pos ⟨hu', hv'⟩, phi_high hu, phi_high hv]
  have he : -Real.log u + -Real.log v = -s := by dsimp [s]; ring
  rw [he]
  unfold psi
  rw [neg_neg, hp, hroot]

/-- Checker A's exact rational inequalities have this real-number interpretation. -/
theorem max_sqrt_enclosure {p lower upper : ℝ}
    (hp : 0 ≤ p) (hl : 0 ≤ lower) (hu : 0 ≤ upper)
    (hlo : lower ≤ p ∨ (4*lower)^2 ≤ p)
    (hup : p ≤ upper) (hsq : p ≤ (4*upper)^2) :
    lower ≤ max p (Real.sqrt p/4) ∧ max p (Real.sqrt p/4) ≤ upper := by
  constructor
  · rcases hlo with hlo | hlo
    · exact le_trans hlo (le_max_left _ _)
    · have hr : 4*lower ≤ Real.sqrt p := Real.le_sqrt_of_sq_le hlo
      exact le_trans (by linarith : lower ≤ Real.sqrt p/4) (le_max_right _ _)
  · apply max_le hup
    have hr : Real.sqrt p ≤ 4*upper := Real.sqrt_le_iff.mpr ⟨by linarith, hsq⟩
    linarith

theorem C_enclosure {u v lower upper : ℝ}
    (hu : (1:ℝ)/16 ≤ u) (hv : (1:ℝ)/16 ≤ v)
    (hl : 0 ≤ lower) (hh : 0 ≤ upper)
    (hlo : lower ≤ u*v ∨ (4*lower)^2 ≤ u*v)
    (hup : u*v ≤ upper) (hsq : u*v ≤ (4*upper)^2) :
    lower ≤ C u v ∧ C u v ≤ upper := by
  rw [C_high_branch hu hv]
  exact max_sqrt_enclosure (mul_nonneg (by linarith) (by linarith)) hl hh hlo hup hsq

end FT23
