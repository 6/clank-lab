import PostLie

/-! Public checks: the two main theorems restated with their full types, and a small
example. `PostLie/Audit.lean` guards the axioms of both theorems. -/

namespace PostLie.PublicChecks

open PostLie

variable {k g n : Type*} [Field k] [CharZero k]
  [LieRing g] [LieAlgebra k g] [LieRing n] [LieAlgebra k n]
  [FiniteDimensional k g] [FiniteDimensional k n]

/-- Theorem 1.1 of the paper. -/
example (e : g ≃ₗ[k] n) (p : Product e) [LieRing.IsNilpotent n]
    (htrace : ∀ x, LinearMap.trace k g (right p x) = 0) :
    LieAlgebra.IsSolvable g :=
  solvable_of_trace_right_eq_zero e p htrace

/-- Corollary 1.2 of the paper. -/
example (e : g ≃ₗ[k] n) [LieRing.IsNilpotent n] [Nontrivial g]
    (hperfect : ⁅(⊤ : LieIdeal k g), (⊤ : LieIdeal k g)⁆ = ⊤) :
    ¬ Nonempty (Product e) :=
  no_product_of_perfect e hperfect

/-- The definition can be satisfied: every Lie algebra carries the zero product over
itself, since then both brackets agree. -/
def zeroProduct (k g : Type*) [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] :
    Product (LinearEquiv.refl k g) where
  mul := 0
  skew := by intro x y; simp
  left_lie := by intro x y z; simp
  derivation := by intro x y z; simp

/-- Its right multiplications are zero, so the theorem applies to it. -/
example [LieRing.IsNilpotent g] : LieAlgebra.IsSolvable g :=
  solvable_of_trace_right_eq_zero (LinearEquiv.refl k g) (zeroProduct k g)
    (fun x => by
      have h : right (zeroProduct k g) x = 0 := LinearMap.ext fun _ => rfl
      rw [h, map_zero])

end PostLie.PublicChecks
