import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.LinearAlgebra.Trace

/-! Post-Lie products with the two brackets identified by a linear equivalence. -/

namespace PostLie

variable {k g n : Type*} [Field k] [CharZero k]
  [LieRing g] [LieAlgebra k g] [LieRing n] [LieAlgebra k n]

/-- Burde–Dekimpe, Definition 2.1 (arXiv:1505.00955v1). -/
structure Product (e : g ≃ₗ[k] n) where
  mul : g →ₗ[k] g →ₗ[k] g
  skew : ∀ x y, mul x y - mul y x = ⁅x, y⁆ - e.symm ⁅e x, e y⁆
  left_lie : ∀ x y z, mul ⁅x, y⁆ z = mul x (mul y z) - mul y (mul x z)
  derivation : ∀ x y z, mul x (e.symm ⁅e y, e z⁆) =
    e.symm ⁅e (mul x y), e z⁆ + e.symm ⁅e y, e (mul x z)⁆

/-- Right multiplication: `right p x y = y · x`. -/
def right {e : g ≃ₗ[k] n} (p : Product e) (x : g) : Module.End k g :=
  p.mul.flip x

end PostLie
