import P16c.Generators
import P16c.Entries

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]

lemma order_four_of_sq_ne_one {M : Type*} [Monoid M] (x : M)
    (h4 : x ^ 4 = 1) (h2 : x ^ 2 ≠ 1) : orderOf x = 4 := by
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)

lemma adjacent01_order (a : K) (ha : a ≠ 0) : orderOf (r a * r₁) = 4 := by
  apply order_four_of_sq_ne_one _ (adjacent01_four a)
  intro h
  have hh := adjacent01_sq_entry a
  rw [h, sub_self] at hh
  exact ha hh.symm
lemma adjacent12_order (b : K) (hb : b ≠ 0) : orderOf (r₁ * r b) = 4 := by
  apply order_four_of_sq_ne_one _ (adjacent12_four b)
  intro h
  have hh := adjacent12_sq_entry b
  rw [h, sub_self] at hh
  exact hb hh.symm
lemma adjacent23_order (a b : K) (ha : a ≠ 0) (hab : a + b ≠ 0) :
    orderOf (r b * r₃ a) = 4 := by
  apply order_four_of_sq_ne_one _ (adjacent23_four a b ha)
  intro h
  have hh := adjacent23_sq_entry a b ha
  rw [h, sub_self] at hh
  exact (div_ne_zero hab ha) hh.symm

/-- L2 in the group of matrix units, with exact adjacent orders. -/
theorem string_relations (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    let g := generators a b ha
    (∀ i, g i ^ 2 = 1) ∧ orderOf (g 0 * g 1) = 4 ∧
      orderOf (g 1 * g 2) = 4 ∧ orderOf (g 2 * g 3) = 4 ∧
      (g 0 * g 2) ^ 2 = 1 ∧ (g 0 * g 3) ^ 2 = 1 ∧ (g 1 * g 3) ^ 2 = 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply Units.ext
    fin_cases i <;> simp [generators, r_sq, r₁_sq, r₃_sq a ha]
  · rw [← orderOf_units]
    simpa using adjacent01_order a ha
  · rw [← orderOf_units]
    simpa using adjacent12_order b hb
  · rw [← orderOf_units]
    simpa using adjacent23_order a b ha hab
  · apply Units.ext
    simpa using string02 a b
  · apply Units.ext
    simpa using string03 a ha
  · apply Units.ext
    simpa using string13 a ha
end P16c
