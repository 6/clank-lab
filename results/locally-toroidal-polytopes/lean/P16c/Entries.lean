import P16c.Identities

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]
open scoped CharTwo
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

lemma v_quadratic_entry (a b : K) (ha : a ≠ 0) :
    (V a b ^ 2 + ((a + b) ^ 2 / a) • V a b + 1 : Mat K) 0 0 = (a + b) ^ 2 / a := by
  simp [V, r, r₁, r₃, Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]
  field_simp
  ring_nf
  simp_all

lemma v_ne_one (a b : K) : V a b ≠ 1 := by
  intro h
  have hh := congrArg (fun M : Mat K => M 0 0) h
  simpa [V, r, r₁, r₃, Matrix.mul_apply, Fin.sum_univ_succ] using hh

lemma adjacent01_sq_entry (a : K) : ((r a * r₁) ^ 2 - 1 : Mat K) 0 0 = a := by
  simp [r, r₁, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  ring_nf
  simp
lemma adjacent12_sq_entry (b : K) : ((r₁ * r b) ^ 2 - 1 : Mat K) 0 0 = b := by
  simp [r, r₁, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  ring_nf
  simp
lemma adjacent23_sq_entry (a b : K) (ha : a ≠ 0) : ((r b * r₃ a) ^ 2 - 1 : Mat K) 0 1 = (a + b) / a := by
  simp [r, r₃, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  ring_nf
  simp_all

lemma tv_ne_vt (a b : K) (ha : a ≠ 0) (hab : a + b ≠ 0) :
    T a b * V a b ≠ V a b * T a b := by
  intro h
  have hz := tv_entry a b
  rw [h, sub_self] at hz
  exact (div_ne_zero hab ha) hz.symm

end P16c
