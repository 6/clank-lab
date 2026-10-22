/- Adapted from proof/lean/ThomsonN9/GramSchmidtFrame.lean,
   aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Data
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-! Explicit well-conditioned three-anchor orthonormal frames. -/

namespace ThomsonN10.Local

set_option autoImplicit false

open InnerProductSpace

noncomputable def gsResidual (x y : R3) : R3 := y-(inner ℝ x y) • x
noncomputable def gsLength (x y : R3) : ℝ := ‖gsResidual x y‖
noncomputable def gsUnit (x y : R3) : R3 := (gsLength x y)⁻¹ • gsResidual x y
noncomputable def gsFinalResidual (x y z : R3) : R3 :=
  z-(inner ℝ x z) • x-(inner ℝ (gsUnit x y) z) • gsUnit x y

theorem gsResidual_inner {x y : R3} (hx : ‖x‖=1) :
    inner ℝ x (gsResidual x y)=0 := by
  simp [gsResidual, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hx]

theorem gsLength_sq {x y : R3} (hx : ‖x‖=1) (hy : ‖y‖=1) :
    (gsLength x y)^2=1-(inner ℝ x y)^2 := by
  unfold gsLength gsResidual
  rw [norm_sub_sq_real, norm_smul, hx, hy, Real.norm_eq_abs, mul_one, sq_abs,
    real_inner_smul_right, real_inner_comm y x]
  ring

theorem gsLength_lower {x y : R3} (hx : ‖x‖=1) (hy : ‖y‖=1)
    (hxy : |inner ℝ x y| ≤ (1/5 : ℝ)) : (2/3 : ℝ) ≤ gsLength x y := by
  have hn : 0 ≤ gsLength x y := norm_nonneg _
  have hs := gsLength_sq hx hy
  have ha : (inner ℝ x y)^2 ≤ (1/5 : ℝ)^2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (inner ℝ x y)) (by norm_num : (0 : ℝ) ≤ 1/5)).mpr hxy
  apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2/3) hn).mp
  nlinarith

theorem gsUnit_norm {x y : R3} (hs : 0 < gsLength x y) : ‖gsUnit x y‖=1 := by
  rw [gsUnit, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  change (gsLength x y)⁻¹ * gsLength x y=1
  exact inv_mul_cancel₀ hs.ne'

theorem gsUnit_inner {x y : R3} (hx : ‖x‖=1) : inner ℝ x (gsUnit x y)=0 := by
  simp [gsUnit, real_inner_smul_right, gsResidual_inner hx]

theorem gsUnit_inner_formula (x y z : R3) :
    inner ℝ (gsUnit x y) z =
      (inner ℝ y z-inner ℝ x y*inner ℝ x z)/gsLength x y := by
  simp only [gsUnit, gsResidual, real_inner_smul_left, inner_sub_left]
  ring

theorem gsUnit_inner_bound {x y z : R3}
    (hx : ‖x‖=1) (hy : ‖y‖=1)
    (hxy : |inner ℝ x y| ≤ (1/5 : ℝ))
    (hxz : |inner ℝ x z| ≤ (5/12 : ℝ))
    (hyz : |inner ℝ y z| ≤ (5/12 : ℝ)) :
    |inner ℝ (gsUnit x y) z| ≤ (3/4 : ℝ) := by
  have hs := gsLength_lower hx hy hxy
  have hsp : 0 < gsLength x y := by linarith
  rw [gsUnit_inner_formula, abs_div, abs_of_pos hsp]
  apply (div_le_iff₀ hsp).mpr
  have hprod : |inner ℝ x y*inner ℝ x z| ≤ (1/12 : ℝ) := by
    rw [abs_mul]
    calc
      _ ≤ (1/5 : ℝ)*(5/12 : ℝ) := mul_le_mul hxy hxz (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hn : |inner ℝ y z-inner ℝ x y*inner ℝ x z| ≤
      |inner ℝ y z|+|inner ℝ x y*inner ℝ x z| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (inner ℝ y z) (-(inner ℝ x y*inner ℝ x z))
  linarith

theorem gsFinalResidual_inner_first {x y z : R3} (hx : ‖x‖=1) :
    inner ℝ x (gsFinalResidual x y z)=0 := by
  simp [gsFinalResidual, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hx, gsUnit_inner hx]

theorem gsFinalResidual_inner_second {x y z : R3} (hx : ‖x‖=1)
    (hs : 0 < gsLength x y) : inner ℝ (gsUnit x y) (gsFinalResidual x y z)=0 := by
  have he : inner ℝ (gsUnit x y) x=0 := by rw [real_inner_comm, gsUnit_inner hx]
  simp [gsFinalResidual, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, gsUnit_norm hs, he]

theorem gsFinalResidual_norm_sq {x y z : R3} (hx : ‖x‖=1) (hz : ‖z‖=1)
    (hs : 0 < gsLength x y) :
    ‖gsFinalResidual x y z‖^2 =
      1-(inner ℝ x z)^2-(inner ℝ (gsUnit x y) z)^2 := by
  rw [gsFinalResidual, norm_sub_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, hx, hz, gsUnit_norm hs, mul_one, sq_abs,
    inner_sub_left, real_inner_smul_left, real_inner_smul_right, gsUnit_inner hx]
  rw [real_inner_comm z x, real_inner_comm z (gsUnit x y)]
  ring

theorem gsFinalResidual_norm_lower {x y z : R3}
    (hx : ‖x‖=1) (hy : ‖y‖=1) (hz : ‖z‖=1)
    (hxy : |inner ℝ x y| ≤ (1/5 : ℝ))
    (hxz : |inner ℝ x z| ≤ (5/12 : ℝ))
    (hyz : |inner ℝ y z| ≤ (5/12 : ℝ)) :
    (1/2 : ℝ) ≤ ‖gsFinalResidual x y z‖ := by
  have hs := gsLength_lower hx hy hxy
  have he := gsUnit_inner_bound hx hy hxy hxz hyz
  have hsq := gsFinalResidual_norm_sq hx hz (by linarith : 0 < gsLength x y)
  have ha : (inner ℝ x z)^2 ≤ (5/12 : ℝ)^2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (inner ℝ x z)) (by norm_num : (0 : ℝ) ≤ 5/12)).mpr hxz
  have hb : (inner ℝ (gsUnit x y) z)^2 ≤ (3/4 : ℝ)^2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (inner ℝ (gsUnit x y) z)) (by norm_num : (0 : ℝ) ≤ 3/4)).mpr he
  apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1/2)
    (norm_nonneg (gsFinalResidual x y z))).mp
  nlinarith

noncomputable def gsBasis (x y z : R3) : OrthonormalBasis (Fin 3) ℝ R3 :=
  gramSchmidtOrthonormalBasis (𝕜 := ℝ) (by simp [R3])
    ![x, gsUnit x y, gsFinalResidual x y z]

theorem gsBasis_apply {x y z : R3}
    (hx : ‖x‖=1) (hy : ‖y‖=1) (hz : ‖z‖=1)
    (hxy : |inner ℝ x y| ≤ (1/5 : ℝ))
    (hxz : |inner ℝ x z| ≤ (5/12 : ℝ))
    (hyz : |inner ℝ y z| ≤ (5/12 : ℝ)) :
    gsBasis x y z 0=x ∧ gsBasis x y z 1=gsUnit x y ∧
      gsBasis x y z 2=‖gsFinalResidual x y z‖⁻¹ • gsFinalResidual x y z := by
  have hs : 0 < gsLength x y := lt_of_lt_of_le (by norm_num) (gsLength_lower hx hy hxy)
  have ht : 0 < ‖gsFinalResidual x y z‖ :=
    lt_of_lt_of_le (by norm_num) (gsFinalResidual_norm_lower hx hy hz hxy hxz hyz)
  have hE := gsUnit_norm hs
  have h01 := gsUnit_inner (y := y) hx
  have h02 := gsFinalResidual_inner_first (y := y) (z := z) hx
  have h12 := gsFinalResidual_inner_second (z := z) hx hs
  have horth : Pairwise fun i j : Fin 3 =>
      inner ℝ (![x, gsUnit x y, gsFinalResidual x y z] i)
        (![x, gsUnit x y, gsFinalResidual x y z] j)=0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [real_inner_comm]
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; norm_num)
  have he0 : gsUnit x y ≠ 0 := norm_ne_zero_iff.mp (by rw [hE]; norm_num)
  have ht0 : gsFinalResidual x y z ≠ 0 := norm_ne_zero_iff.mp ht.ne'
  constructor
  · unfold gsBasis
    simpa [hx] using gramSchmidtOrthonormalBasis_apply_of_orthogonal
      (𝕜 := ℝ) (by simp [R3]) horth (i := (0 : Fin 3)) hx0
  constructor
  · unfold gsBasis
    simpa [hE] using gramSchmidtOrthonormalBasis_apply_of_orthogonal
      (𝕜 := ℝ) (by simp [R3]) horth (i := (1 : Fin 3)) he0
  · unfold gsBasis
    simpa using gramSchmidtOrthonormalBasis_apply_of_orthogonal
      (𝕜 := ℝ) (by simp [R3]) horth (i := (2 : Fin 3)) ht0

theorem gsBasis_coordinates {x y z : R3}
    (hx : ‖x‖=1) (hy : ‖y‖=1) (hz : ‖z‖=1)
    (hxy : |inner ℝ x y| ≤ (1/5 : ℝ))
    (hxz : |inner ℝ x z| ≤ (5/12 : ℝ))
    (hyz : |inner ℝ y z| ≤ (5/12 : ℝ)) (w : R3) :
    (gsBasis x y z).repr w 0=inner ℝ x w ∧
    (gsBasis x y z).repr w 1=(inner ℝ y w-inner ℝ x y*inner ℝ x w)/gsLength x y ∧
    (gsBasis x y z).repr w 2=
      (inner ℝ z w-inner ℝ x z*inner ℝ x w-
        inner ℝ (gsUnit x y) z*(gsBasis x y z).repr w 1)/‖gsFinalResidual x y z‖ := by
  obtain ⟨h0,h1,h2⟩ := gsBasis_apply hx hy hz hxy hxz hyz
  constructor
  · rw [OrthonormalBasis.repr_apply_apply, h0]
  constructor
  · rw [OrthonormalBasis.repr_apply_apply, h1, gsUnit_inner_formula]
  · rw [OrthonormalBasis.repr_apply_apply, h2, real_inner_smul_left,
      OrthonormalBasis.repr_apply_apply, h1]
    simp only [gsFinalResidual, inner_sub_left, real_inner_smul_left]
    ring

end ThomsonN10.Local
