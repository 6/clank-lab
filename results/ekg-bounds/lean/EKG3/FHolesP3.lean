import EKG3.FPrimeBoundsP3
import EKG.HoleCounting

namespace EKG3.P3.FarTail
open EKG Real

/-- A hole may be compared with any larger integer `b`. This is also the
small-hole control: take `b=10^153`, without applying an asymptotic estimate
at the small hole itself. -/
theorem hole_envelope (hrs : TailPiBounds) {u h b : ℕ}
    (hh : 15 ≤ h) (hnp : ¬ h.Prime) (hbelow : h < frontier canonical u)
    (hfree : ¬ UsedBefore actualA (u+1) h) (hb : h ≤ b)
    (hbig : (10:ℝ)^153 ≤ b) :
    (frontier canonical u : ℝ) ≤ (1 + gamma b) * b := by
  have hraw := canonical.missing_composite_bound hh hnp hbelow hfree
  have hraw' : frontier canonical u ≤ h + 2*h.minFac*(13*Nat.primeCounting (Nat.sqrt h)+724) := by
    omega
  have hc : (frontier canonical u : ℝ) ≤ (h:ℝ) +
      2*(h.minFac:ℝ)*(13*(Nat.primeCounting (Nat.sqrt h):ℝ)+724) := by
    exact_mod_cast hraw'
  have hfac : (h.minFac:ℝ) ≤ sqrt b := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    exact_mod_cast (Nat.minFac_sq_le_self (by omega : 0<h) hnp).trans hb
  have hpi : (Nat.primeCounting (Nat.sqrt h):ℝ) ≤ sqrtPrimeCount b := by
    rw [← primeCounting_sqrt_nat_eq]
    exact_mod_cast Nat.monotone_primeCounting (Nat.sqrt_le_sqrt hb)
  have hp := sqrt_prime_bound hrs hbig
  have hcnt : (Nat.primeCounting (Nat.sqrt h):ℝ) ≤
      (2*1.045/log b) * sqrt b := hpi.trans hp
  have hL : 0 < log (b:ℝ) := by have := (large_parameters hbig).1; linarith
  have hroot : 0 < sqrt (b:ℝ) := by have := (large_parameters hbig).2.1; linarith
  have hbpos : (0:ℝ) ≤ b := by positivity
  have hmul := mul_le_mul hfac (by linarith :
    13*(Nat.primeCounting (Nat.sqrt h):ℝ)+724 ≤
      13*((2*1.045/log b)*sqrt b)+724)
    (by positivity : (0:ℝ) ≤ 13*(Nat.primeCounting (Nat.sqrt h):ℝ)+724)
    (sqrt_nonneg (b:ℝ))
  have hble : (h:ℝ) ≤ b := by exact_mod_cast hb
  have hid : (1+gamma b)*(b:ℝ) = (b:ℝ) +
      2*sqrt b*(13*((2*1.045/log b)*sqrt b)+724) := by
    unfold gamma
    have hsq := Real.sq_sqrt hbpos
    field_simp
    nlinarith [Real.mul_self_sqrt hbpos]
  rw [hid]
  nlinarith

theorem large_hole_lower (hrs : TailPiBounds) {u h : ℕ}
    (he : (9:ℝ)*10^155 < frontier canonical u)
    (hh : 15 ≤ h) (hnp : ¬ h.Prime) (hbelow : h < frontier canonical u)
    (hfree : ¬ UsedBefore actualA (u+1) h) :
    (frontier canonical u : ℝ) < (1+0.1542456)*(h:ℝ) := by
  have hhbig : 10^153 ≤ h := by
    by_contra hn
    have henv := hole_envelope hrs hh hnp hbelow hfree (b := 10^153)
      (by omega) (by norm_num)
    have hg := (numeric_bounds (x := (10:ℝ)^153) (by rfl)).2.2.2.2.1
    norm_cast at henv
    have hb : (frontier canonical u : ℝ) < (1+0.1542456)*(10:ℝ)^153 := by
      have hmul := mul_lt_mul_of_pos_right hg (by positivity : (0:ℝ)<10^153)
      push_cast at henv
      linarith
    have hr := ratio_checks.2.2.2.2.1
    linarith
  have henv := hole_envelope hrs hh hnp hbelow hfree (le_refl h)
    (by exact_mod_cast hhbig)
  have hg := (numeric_bounds (x := (h:ℝ)) (by exact_mod_cast hhbig)).2.2.2.2.1
  have hp : (0:ℝ) < (h:ℝ) := by exact_mod_cast (show 0<h by omega)
  have hm := mul_lt_mul_of_pos_right hg hp
  linarith

end EKG3.P3.FarTail
