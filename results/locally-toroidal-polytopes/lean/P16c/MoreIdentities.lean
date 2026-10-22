import P16c.Identities

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]
open scoped CharTwo
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

lemma v_cubic (a b : K) (ha : a ≠ 0) :
    (V a b + 1) * (V a b ^ 2 + ((a + b) ^ 2 / a) • V a b + 1) = 0 := by
  matrix_ring <;> field_simp <;> ring_nf <;> simp_all

lemma v₂_cubic (a b : K) (ha : a ≠ 0) :
    (V₂ a b + 1) * (V₂ a b ^ 2 + ((a + b) ^ 2 / a) • V₂ a b + 1) = 0 := by
  matrix_ring <;> field_simp <;> ring_nf <;> simp_all

lemma v₂_on_fixed (a b : K) (ha : a ≠ 0) :
    (V₂ a b ^ 2 + ((a + b) ^ 2 / a) • V₂ a b + 1) *
      (V a b ^ 2 + ((a + b) ^ 2 / a) • V a b + 1) = 0 := by
  matrix_ring <;> field_simp <;> ring_nf <;> simp_all

lemma r₁_v (a b : K) (ha : a ≠ 0) :
    r₁ * V a b * r₁ = V a b ^ 2 + (((a + b) ^ 2 / a) + 1) • V a b +
      (((a + b) ^ 2 / a) + 1) • (1 : Mat K) := by
  matrix_ring <;> field_simp <;> ring_nf <;> simp_all

end P16c
