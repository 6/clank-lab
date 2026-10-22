import P16c.MatrixDefs

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]
open scoped CharTwo
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

macro "matrix_ring" : tactic => `(tactic|
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [r, r₁, r₃, T, V, T₂, V₂, Matrix.mul_apply, Fin.sum_univ_succ,
      pow_succ, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply] <;>
    ring_nf <;> simp_all))

lemma r_sq (a : K) : r a ^ 2 = 1 := by matrix_ring
lemma r₁_sq : (r₁ : Mat K) ^ 2 = 1 := by matrix_ring
lemma r₃_sq (a : K) (ha : a ≠ 0) : r₃ a ^ 2 = 1 := by
  matrix_ring <;> simp [ha]

lemma string02 (a b : K) : (r a * r b) ^ 2 = 1 := by matrix_ring
lemma string03 (a : K) (ha : a ≠ 0) : (r a * r₃ a) ^ 2 = 1 := by
  matrix_ring <;> simp [ha]
lemma string13 (a : K) (ha : a ≠ 0) : ((r₁ : Mat K) * r₃ a) ^ 2 = 1 := by
  matrix_ring <;> simp [ha]

lemma adjacent01_four (a : K) : (r a * r₁) ^ 4 = 1 := by matrix_ring
lemma adjacent12_four (b : K) : (r₁ * r b) ^ 4 = 1 := by matrix_ring
lemma adjacent23_four (a b : K) (ha : a ≠ 0) : (r b * r₃ a) ^ 4 = 1 := by
  matrix_ring <;> field_simp <;> ring_nf <;> simp

lemma t_quadratic (a b : K) : T a b ^ 2 + (a + b) • T a b + 1 = 0 := by
  matrix_ring
lemma t₂_quadratic (a b : K) : T₂ a b ^ 2 + (a + b) • T₂ a b + 1 = 0 := by
  matrix_ring
lemma t_commute (a b : K) : T a b * T₂ a b = T₂ a b * T a b := by matrix_ring
lemma v_commute (a b : K) (ha : a ≠ 0) : V a b * V₂ a b = V₂ a b * V a b := by
  matrix_ring <;> field_simp <;> ring_nf <;> simp

lemma r₁_t (a b : K) : r₁ * T a b * r₁ = T₂ a b := rfl
lemma r₁_t₂ (a b : K) : r₁ * T₂ a b * r₁ = T a b := by matrix_ring
lemma r₂_t (a b : K) : r b * T a b * r b = T a b := by matrix_ring
lemma r₂_t₂ (a b : K) : r b * T₂ a b * r b = T₂ a b + (a + b) • (1 : Mat K) := by
  matrix_ring
lemma r₂_v (a b : K) : r b * V a b * r b = V₂ a b := rfl
lemma r₂_v₂ (a b : K) : r b * V₂ a b * r b = V a b := by matrix_ring
lemma r₁_v₂ (a b : K) : r₁ * V₂ a b * r₁ = V₂ a b := by matrix_ring

lemma tv_entry (a b : K) : (T a b * V a b - V a b * T a b) 0 1 = (a + b) / a := by
  simp [T, V, r, r₁, r₃, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.sub_apply]
  ring_nf
  simp

end P16c
