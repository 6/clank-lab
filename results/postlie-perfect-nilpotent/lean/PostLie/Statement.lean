import PostLie.Action
import PostLie.Solvability

/-! Post-Lie products with the two brackets identified by a linear equivalence. -/

namespace PostLie

variable {k g n : Type*} [Field k] [CharZero k]
  [LieRing g] [LieAlgebra k g] [LieRing n] [LieAlgebra k n]
  [FiniteDimensional k g] [FiniteDimensional k n]

/-- Nilpotent second bracket and traceless right multiplications force solvability. -/
theorem solvable_of_trace_right_eq_zero (e : g ≃ₗ[k] n) (p : Product e)
    [LieRing.IsNilpotent n]
    (htrace : ∀ x, LinearMap.trace k g (right p x) = 0) :
    LieAlgebra.IsSolvable g := by
  exact solvable_of_invertible_cocycle (action p) e (identification_isCocycle p)
    (trace_action_eq_trace_ad p htrace)

/-- A nonzero perfect Lie algebra admits no post-Lie product with a nilpotent bracket. -/
theorem no_product_of_perfect (e : g ≃ₗ[k] n)
    [LieRing.IsNilpotent n] [Nontrivial g]
    (hperfect : ⁅(⊤ : LieIdeal k g), (⊤ : LieIdeal k g)⁆ = ⊤) :
    ¬ Nonempty (Product e) := by
  rintro ⟨p⟩
  have := solvable_of_trace_right_eq_zero e p (trace_right_of_perfect p hperfect)
  have hlt := LieAlgebra.derivedSeries_lt_top_of_solvable k g
  change ⁅(⊤ : LieIdeal k g), (⊤ : LieIdeal k g)⁆ < ⊤ at hlt
  exact (ne_of_lt hlt) hperfect

end PostLie
