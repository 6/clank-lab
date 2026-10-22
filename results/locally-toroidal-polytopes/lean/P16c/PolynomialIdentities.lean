import P16c.MatrixDefs

namespace P16c
open Polynomial
open scoped CharTwo
variable {K : Type*} [Field K] [CharP K 2]

lemma eval_split_quadratic (M : Mat K) (m : K) (hm : m ≠ 0) :
    aeval M ((X - C m) * (X - C m⁻¹)) = M ^ 2 + traceParam m • M + 1 := by
  simp only [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  simp [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, hm,
    pow_two, traceParam, add_smul]
  module
end P16c
