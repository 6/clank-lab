/- Adapted from proof/lean/ThomsonN9/GramStability.lean,
   aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Data

/-! Conservative scalar perturbation bounds for Gram--Schmidt coordinates. -/

namespace ThomsonN10.Local

set_option autoImplicit false

theorem abs_sub_le_sum_abs (a b : ℝ) : |a-b| ≤ |a|+|b| := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)

theorem abs_product_difference {a b c d da db : ℝ}
    (ha : |a-c| ≤ da) (hb : |b-d| ≤ db) (hc : |c| ≤ 1) (hbb : |b| ≤ 1) :
    |a*b-c*d| ≤ da+db := by
  calc
    |a*b-c*d| = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = |a-c| * |b| + |c| * |b-d| := by rw [abs_mul, abs_mul]
    _ ≤ |a-c|+|b-d| := by
      have h1 := mul_le_mul_of_nonneg_left hbb (abs_nonneg (a-c))
      have h2 := mul_le_mul_of_nonneg_right hc (abs_nonneg (b-d))
      nlinarith
    _ ≤ da+db := add_le_add ha hb

theorem inverse_difference_bound {s t ds : ℝ}
    (hs : (1/2 : ℝ) ≤ s) (ht : (1/2 : ℝ) ≤ t) (hd : |s-t| ≤ ds) :
    |s⁻¹-t⁻¹| ≤ 4*ds := by
  have hsp : 0 < s := by linarith
  have htp : 0 < t := by linarith
  have hst : (1/4 : ℝ) ≤ s*t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr ht)]
  have hds : 0 ≤ ds := le_trans (abs_nonneg _) hd
  have hid : s⁻¹-t⁻¹ = (t-s)/(s*t) := by field_simp [hsp.ne', htp.ne'] <;> ring
  rw [hid, abs_div, abs_of_pos (mul_pos hsp htp), abs_sub_comm]
  apply (div_le_iff₀ (mul_pos hsp htp)).mpr
  calc
    |s-t| ≤ ds := hd
    _ = (4*ds)*(1/4 : ℝ) := by ring
    _ ≤ (4*ds)*(s*t) := mul_le_mul_of_nonneg_left hst (by positivity)

theorem quotient_difference_bound {a b s t da ds K : ℝ}
    (hs : (1/2 : ℝ) ≤ s) (ht : (1/2 : ℝ) ≤ t)
    (hab : |a-b| ≤ da) (hd : |s-t| ≤ ds) (hb : |b| ≤ K) :
    |a/s-b/t| ≤ 2*da+4*K*ds := by
  have hsp : 0 < s := by linarith
  have htp : 0 < t := by linarith
  have hda : 0 ≤ da := le_trans (abs_nonneg _) hab
  have hds : 0 ≤ ds := le_trans (abs_nonneg _) hd
  have hK : 0 ≤ K := le_trans (abs_nonneg _) hb
  have hi : |s⁻¹-t⁻¹| ≤ 4*ds := inverse_difference_bound hs ht hd
  have his : |s⁻¹| ≤ 2 := by
    rw [abs_of_pos (inv_pos.mpr hsp)]
    apply (inv_le_iff_one_le_mul₀ hsp).mpr
    linarith
  calc
    |a/s-b/t| = |(a-b)*s⁻¹+b*(s⁻¹-t⁻¹)| := by congr 1; simp only [div_eq_mul_inv]; ring
    _ ≤ |a-b| * |s⁻¹| + |b| * |s⁻¹-t⁻¹| := by
      simpa only [abs_mul] using abs_add_le ((a-b)*s⁻¹) (b*(s⁻¹-t⁻¹))
    _ ≤ da*2+K*(4*ds) := by gcongr
    _ = 2*da+4*K*ds := by ring

theorem square_root_difference_bound {s t d : ℝ}
    (hs : (1/2 : ℝ) ≤ s) (ht : (1/2 : ℝ) ≤ t)
    (hd : |s^2-t^2| ≤ d) : |s-t| ≤ d := by
  have hst : 1 ≤ s+t := by linarith
  calc
    |s-t| ≤ |s-t| * (s+t) := le_mul_of_one_le_right (abs_nonneg _) hst
    _ = |s^2-t^2| := by
      rw [← abs_of_nonneg (by linarith : 0 ≤ s+t), ← abs_mul]
      congr 1
      ring
    _ ≤ d := hd

theorem norm_difference_from_coordinates {u v : R3} {δ : ℝ}
    (hd : 0 ≤ δ) (h : ∀ j, |u j-v j| ≤ 650*δ) :
    ‖u-v‖^2 ≤ 3*(650*δ)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hh : ∀ j : Fin 3, ((u-v) j)^2 ≤ (650*δ)^2 := by
    intro j
    simpa only [PiLp.sub_apply, sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (h j)
  calc
    (∑ j : Fin 3, ((u-v) j)^2) ≤ ∑ _j : Fin 3, (650*δ)^2 :=
      Finset.sum_le_sum (fun j _ => hh j)
    _ = 3*(650*δ)^2 := by simp

theorem configuration_difference_from_coordinates {x p : Configuration} {δ : ℝ}
    (hd : 0 ≤ δ) (h : ∀ i j, |(x i) j-(p i) j| ≤ 650*δ) :
    (∑ i, ‖x i-p i‖^2) ≤ (10000*δ)^2 := by
  have hh : (∑ i, ‖x i-p i‖^2) ≤ ∑ _i : Fin 10, 3*(650*δ)^2 :=
    Finset.sum_le_sum (fun i _ => norm_difference_from_coordinates hd (h i))
  norm_num at hh
  nlinarith [sq_nonneg δ]

theorem difference_of_differences_bound {a b c d da db : ℝ}
    (ha : |a-c| ≤ da) (hb : |b-d| ≤ db) : |(a-b)-(c-d)| ≤ da+db := by
  calc
    |(a-b)-(c-d)| = |(a-c)-(b-d)| := by congr 1; ring
    _ ≤ |a-c|+|b-d| := abs_sub_le_sum_abs _ _
    _ ≤ da+db := add_le_add ha hb

/-- Scalar data of one point in a three-anchor Gram--Schmidt frame. -/
structure TriangularScalarData where
  a : ℝ
  d : ℝ
  e : ℝ
  u : ℝ
  v : ℝ
  w : ℝ
  s : ℝ
  t : ℝ
  b : ℝ
  y : ℝ
  z : ℝ
  ha : |a| ≤ 1
  hd : |d| ≤ 1
  he : |e| ≤ 1
  hu : |u| ≤ 1
  hv : |v| ≤ 1
  hw : |w| ≤ 1
  hb : |b| ≤ 1
  hy : |y| ≤ 1
  hs : (1/2 : ℝ) ≤ s
  ht : (1/2 : ℝ) ≤ t
  s_sq : s^2=1-a^2
  b_eq : b=(e-a*d)/s
  t_sq : t^2=1-d^2-b^2
  y_eq : y=(v-a*u)/s
  z_eq : z=(w-d*u-b*y)/t

theorem triangular_scalar_stability (P Q : TriangularScalarData) {δ : ℝ}
    (ha : |P.a-Q.a| ≤ δ) (hd : |P.d-Q.d| ≤ δ) (he : |P.e-Q.e| ≤ δ)
    (hu : |P.u-Q.u| ≤ δ) (hv : |P.v-Q.v| ≤ δ) (hw : |P.w-Q.w| ≤ δ) :
    |P.y-Q.y| ≤ 22*δ ∧ |P.z-Q.z| ≤ 646*δ := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) ha
  have hs_sq : |P.s^2-Q.s^2| ≤ 2*δ := by
    have h := abs_product_difference ha ha Q.ha P.ha
    rw [P.s_sq, Q.s_sq]
    calc
      |(1-P.a^2)-(1-Q.a^2)| = |P.a*P.a-Q.a*Q.a| := by
        rw [← abs_neg]
        congr 1
        ring
      _ ≤ 2*δ := by linarith
  have hs : |P.s-Q.s| ≤ 2*δ := square_root_difference_bound P.hs Q.hs hs_sq
  have hnum_b : |(P.e-P.a*P.d)-(Q.e-Q.a*Q.d)| ≤ 3*δ := by
    have hprod := abs_product_difference ha hd Q.ha P.hd
    have h := difference_of_differences_bound he hprod
    linarith
  have hnum_y : |(P.v-P.a*P.u)-(Q.v-Q.a*Q.u)| ≤ 3*δ := by
    have hprod := abs_product_difference ha hu Q.ha P.hu
    have h := difference_of_differences_bound hv hprod
    linarith
  have hbQ : |Q.e-Q.a*Q.d| ≤ 2 := by
    have hp : |Q.a*Q.d| ≤ 1 := by
      rw [abs_mul]
      simpa using mul_le_mul Q.ha Q.hd (abs_nonneg Q.d) (by norm_num : (0 : ℝ) ≤ 1)
    have h := abs_sub_le_sum_abs Q.e (Q.a*Q.d)
    linarith [Q.he]
  have hyQ : |Q.v-Q.a*Q.u| ≤ 2 := by
    have hp : |Q.a*Q.u| ≤ 1 := by
      rw [abs_mul]
      simpa using mul_le_mul Q.ha Q.hu (abs_nonneg Q.u) (by norm_num : (0 : ℝ) ≤ 1)
    have h := abs_sub_le_sum_abs Q.v (Q.a*Q.u)
    linarith [Q.hv]
  have hb : |P.b-Q.b| ≤ 22*δ := by
    rw [P.b_eq, Q.b_eq]
    have h := quotient_difference_bound P.hs Q.hs hnum_b hs hbQ
    nlinarith
  have hy : |P.y-Q.y| ≤ 22*δ := by
    rw [P.y_eq, Q.y_eq]
    have h := quotient_difference_bound P.hs Q.hs hnum_y hs hyQ
    nlinarith
  have ht_sq : |P.t^2-Q.t^2| ≤ 46*δ := by
    have hdd := abs_product_difference hd hd Q.hd P.hd
    have hbb := abs_product_difference hb hb Q.hb P.hb
    have hid : |P.t^2-Q.t^2| = |(P.d*P.d+P.b*P.b)-(Q.d*Q.d+Q.b*Q.b)| := by
      rw [P.t_sq, Q.t_sq, ← abs_neg]
      congr 1
      ring
    rw [hid]
    calc
      _ = |(P.d*P.d-Q.d*Q.d)+(P.b*P.b-Q.b*Q.b)| := by congr 1; ring
      _ ≤ |P.d*P.d-Q.d*Q.d|+|P.b*P.b-Q.b*Q.b| := abs_add_le _ _
      _ ≤ 46*δ := by linarith
  have ht : |P.t-Q.t| ≤ 46*δ := square_root_difference_bound P.ht Q.ht ht_sq
  have hnum_z : |(P.w-P.d*P.u-P.b*P.y)-(Q.w-Q.d*Q.u-Q.b*Q.y)| ≤ 47*δ := by
    have hdu := abs_product_difference hd hu Q.hd P.hu
    have hby := abs_product_difference hb hy Q.hb P.hy
    have h := difference_of_differences_bound
      (difference_of_differences_bound hw hdu) hby
    linarith
  have hzQ : |Q.w-Q.d*Q.u-Q.b*Q.y| ≤ 3 := by
    have hp1 : |Q.d*Q.u| ≤ 1 := by
      rw [abs_mul]
      simpa using mul_le_mul Q.hd Q.hu (abs_nonneg Q.u) (by norm_num : (0 : ℝ) ≤ 1)
    have hp2 : |Q.b*Q.y| ≤ 1 := by
      rw [abs_mul]
      simpa using mul_le_mul Q.hb Q.hy (abs_nonneg Q.y) (by norm_num : (0 : ℝ) ≤ 1)
    have h1 := abs_sub_le_sum_abs Q.w (Q.d*Q.u)
    have h2 := abs_sub_le_sum_abs (Q.w-Q.d*Q.u) (Q.b*Q.y)
    linarith [Q.hw]
  refine ⟨hy, ?_⟩
  rw [P.z_eq, Q.z_eq]
  have h := quotient_difference_bound P.ht Q.ht hnum_z ht hzQ
  nlinarith

end ThomsonN10.Local
