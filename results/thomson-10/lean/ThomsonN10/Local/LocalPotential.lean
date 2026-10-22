/- Adapted from proof/lean/ThomsonN9/LocalPotential.lean,
   aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Data

/-! Algebraic local-potential bounds, avoiding a third-derivative remainder. -/

namespace ThomsonN10.Local

noncomputable def reciprocalSqrtCubic (q : ℝ) : ℝ := 1-q/2+3*q^2/8-5*q^3/16

theorem reciprocalSqrtCubic_le {q : ℝ} (hq : -1 < q) (hq1 : q ≤ 1) :
    reciprocalSqrtCubic q ≤ 1 / Real.sqrt (1+q) := by
  have hquad : 0 ≤ 1+q+q^2 := by nlinarith [sq_nonneg (q+1/2)]
  have hprod : 0 ≤ (1-q)*(1+q+q^2) := mul_nonneg (by linarith) hquad
  have hfactor : 0 ≤ 140-56*q+35*q^2-25*q^3 := by
    nlinarith [sq_nonneg q]
  have hrem : 0 ≤ q^4*(140-56*q+35*q^2-25*q^3)/256 :=
    div_nonneg (mul_nonneg (by positivity) hfactor) (by norm_num)
  have hid : 1-(1+q)*(reciprocalSqrtCubic q)^2 =
      q^4*(140-56*q+35*q^2-25*q^3)/256 := by
    unfold reciprocalSqrtCubic
    ring
  have hs : 0 < Real.sqrt (1+q) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : (Real.sqrt (1+q))^2 = 1+q := Real.sq_sqrt (by linarith)
  have hsq : (reciprocalSqrtCubic q * Real.sqrt (1+q))^2 ≤ 1 := by
    rw [mul_pow, hs2]
    nlinarith [hid, hrem]
  rw [le_div_iff₀ hs]
  nlinarith [sq_nonneg (reciprocalSqrtCubic q * Real.sqrt (1+q)-1)]

theorem cubic_direction_lower {a c : ℝ} (ha : a ≤ c) :
    -c^3 ≤ 3*a*c^2/2-5*a^3/2 := by
  have hquad : 0 ≤ 5*a^2+5*a*c+2*c^2 := by
    nlinarith [sq_nonneg (a+c/2), sq_nonneg c]
  have hp := mul_nonneg (sub_nonneg.mpr ha) hquad
  nlinarith

theorem reciprocalSqrtCubic_local_lower {a c : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1/200) (ha : |a| ≤ c) :
    1-a-c^2/2+3*a^2/2-(51/50 : ℝ)*c^3 ≤ reciprocalSqrtCubic (2*a+c^2) := by
  obtain ⟨hal, hau⟩ := abs_le.mp ha
  have ha2 : a^2 ≤ c^2 := by nlinarith
  have hc2 : c^2 ≤ (1/40000 : ℝ) := by nlinarith
  have hc3 : c^3 ≤ (1/8000000 : ℝ) := by
    calc
      c^3 = c*c^2 := by ring
      _ ≤ (1/200 : ℝ)*(1/40000) :=
        mul_le_mul hc1 hc2 (sq_nonneg c) (by norm_num)
      _ = 1/8000000 := by norm_num
  have hcoef : 15*c/4+15*c^2/8+5*c^3/16 ≤ (1/50 : ℝ) := by
    nlinarith
  have ha2c2 := mul_le_mul_of_nonneg_right ha2 (sq_nonneg c)
  have hac4 := mul_le_mul_of_nonneg_right hau (pow_nonneg hc 4)
  have hlead := cubic_direction_lower hau
  have hrest := mul_nonneg (pow_nonneg hc 3) (sub_nonneg.mpr hcoef)
  unfold reciprocalSqrtCubic
  nlinarith [pow_nonneg hc 4]

theorem reciprocalSqrt_local_lower {a c : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1/200) (ha : |a| ≤ c) :
    1-a-c^2/2+3*a^2/2-(51/50 : ℝ)*c^3 ≤ 1 / Real.sqrt (1+2*a+c^2) := by
  obtain ⟨hal, hau⟩ := abs_le.mp ha
  have hlow : -1 < 2*a+c^2 := by nlinarith [sq_nonneg c]
  have hhigh : 2*a+c^2 ≤ 1 := by nlinarith
  have h := (reciprocalSqrtCubic_local_lower hc hc1 ha).trans
    (reciprocalSqrtCubic_le hlow hhigh)
  simpa only [add_assoc] using h

theorem algebraic_local_constants :
    (1/50 : ℝ) ≤ 7/100-(2477/100)*(1/500)-(1107/400)*(1/500)^2 := by
  norm_num

theorem pair_potential_algebraic_lower {d w : R3}
    (hd : 0 < ‖d‖) (hw : ‖w‖ ≤ ‖d‖ / 200) :
    1/‖d‖ - inner ℝ d w / ‖d‖^3 +
      (3*(inner ℝ d w)^2-‖d‖^2*‖w‖^2)/(2*‖d‖^5) -
      (51/50 : ℝ)*‖w‖^3/‖d‖^4 ≤ 1/‖d+w‖ := by
  let D := ‖d‖
  let W := ‖w‖
  let a := inner ℝ d w / D^2
  let c := W/D
  have hD : 0 < D := hd
  have hD0 : D ≠ 0 := ne_of_gt hD
  have hc : 0 ≤ c := div_nonneg (norm_nonneg w) hD.le
  have hc1 : c ≤ (1/200 : ℝ) := by
    dsimp [c, W, D]
    apply (div_le_iff₀ hd).mpr
    linarith
  have ha : |a| ≤ c := by
    dsimp [a, c]
    rw [abs_div, abs_of_nonneg (sq_nonneg D)]
    apply (div_le_div_iff₀ (sq_pos_of_pos hD) hD).mpr
    have hp := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm d w) hD.le
    change |inner ℝ d w| * D ≤ D * W * D at hp
    nlinarith
  have hbase := reciprocalSqrt_local_lower hc hc1 ha
  have hq : 0 < 1+2*a+c^2 := by
    have hal := (abs_le.mp ha).1
    nlinarith [sq_nonneg c]
  have hnormsq : ‖d+w‖^2 = D^2*(1+2*a+c^2) := by
    rw [norm_add_sq_real]
    dsimp [a, c, D, W]
    field_simp
    <;> ring
  have hroot : (D*Real.sqrt (1+2*a+c^2))^2 = D^2*(1+2*a+c^2) := by
    rw [mul_pow, Real.sq_sqrt hq.le]
  have hnorm : ‖d+w‖ = D*Real.sqrt (1+2*a+c^2) := by
    have hp := mul_nonneg hD.le (Real.sqrt_nonneg (1+2*a+c^2))
    nlinarith [norm_nonneg (d+w)]
  calc
    1/‖d‖ - inner ℝ d w / ‖d‖^3 +
        (3*(inner ℝ d w)^2-‖d‖^2*‖w‖^2)/(2*‖d‖^5) -
        (51/50 : ℝ)*‖w‖^3/‖d‖^4 =
      (1/D)*(1-a-c^2/2+3*a^2/2-(51/50 : ℝ)*c^3) := by
        dsimp [a, c, D, W]
        field_simp
        <;> ring
    _ ≤ (1/D)*(1/Real.sqrt (1+2*a+c^2)) :=
      mul_le_mul_of_nonneg_left hbase (le_of_lt (one_div_pos.mpr hD))
    _ = 1/‖d+w‖ := by
      rw [hnorm]
      simp only [one_div, mul_inv]

end ThomsonN10.Local
