import FT23.GeneratorInverse

noncomputable section
open Set
namespace FT23

lemma kink_superadditive {x y L : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hL : 0 ≤ L) :
    max x (2*x-2*L) + max y (2*y-2*L) ≤ max (x+y) (2*(x+y)-2*L) := by
  by_cases hxl : x ≤ 2*L <;> by_cases hyl : y ≤ 2*L
  · rw [max_eq_left (by linarith : 2*x-2*L ≤ x),
      max_eq_left (by linarith : 2*y-2*L ≤ y)]
    exact le_max_left _ _
  · rw [max_eq_left (by linarith : 2*x-2*L ≤ x),
      max_eq_right (by linarith : y ≤ 2*y-2*L)]
    exact le_trans (by linarith) (le_max_right _ _)
  · rw [max_eq_right (by linarith : x ≤ 2*x-2*L),
      max_eq_left (by linarith : 2*y-2*L ≤ y)]
    exact le_trans (by linarith) (le_max_right _ _)
  · rw [max_eq_right (by linarith : x ≤ 2*x-2*L),
      max_eq_right (by linarith : y ≤ 2*y-2*L)]
    exact le_trans (by linarith) (le_max_right _ _)

lemma phi_product {u v : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) (hv : v ∈ Ioc (0:ℝ) 1) :
    phi u + phi v ≤ phi (u*v) := by
  have huLog : 0 ≤ -Real.log u := neg_nonneg.mpr (Real.log_nonpos hu.1.le hu.2)
  have hvLog : 0 ≤ -Real.log v := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2)
  have hL : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h := kink_superadditive huLog hvLog hL
  have he (w : ℝ) : phi w = max (-Real.log w) (2*(-Real.log w)-2*Real.log 4) := by
    unfold phi
    rw [log_sixteen]
    congr 1
    ring
  rw [he u, he v, he (u*v), Real.log_mul hu.1.ne' hv.1.ne']
  convert h using 1 <;> congr 1 <;> ring

theorem exact_PQD : PQD C := by
  intro u hu v hv
  by_cases hu0 : u = 0
  · simp [C, hu0]
  by_cases hv0 : v = 0
  · simp [C, hv0]
  have hu' : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have hv' : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hv0)
  have hm := psi_antitone (phi_product ⟨hu', hu.2⟩ ⟨hv', hv.2⟩)
  rw [psi_phi_positive (mul_pos hu' hv')] at hm
  simpa [C, hu', hv'] using hm

end FT23
