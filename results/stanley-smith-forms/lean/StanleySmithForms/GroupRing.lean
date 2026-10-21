import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Abel

/-!
# A relation for `X₃` in the integral group ring of `Sₙ`

With `s = (1 3)`, `t = (2 3)` and `u = (1 2)`, the Jucys–Murphy element is
`X₃ = s + t`. Then `X₃² = 2 + st + ts` and `X₃ u = su + tu = ts + st`, the two
3-cycles on `{1, 2, 3}`, so `X₃ (X₃ - u) = 2`; likewise `(X₃ - u) X₃ = 2`.
The identity holds in `ℤ[Sₙ]` for every `n ≥ 3`. Points `1, 2, 3` are
`0, 1, 2 : Fin n`, and the product of permutations is composition,
`(σ * τ) x = σ (τ x)`.
-/

namespace StanleySmithForms

open MonoidAlgebra

/-- The relations between three transpositions on three distinct points used
below. -/
theorem swap_relations {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Equiv.swap a c * Equiv.swap b c = Equiv.swap b c * Equiv.swap a b ∧
    Equiv.swap b c * Equiv.swap a c = Equiv.swap a c * Equiv.swap a b ∧
    Equiv.swap a b * Equiv.swap a c = Equiv.swap a c * Equiv.swap b c ∧
    Equiv.swap a b * Equiv.swap b c = Equiv.swap b c * Equiv.swap a c := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext x <;>
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    split_ifs <;> simp_all

/-- The identity for any three distinct points `a, b, c`, with
`X = (a c) + (b c)` and `T = (a b)`. -/
theorem swap_identity {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (single (Equiv.swap a c) 1 + single (Equiv.swap b c) 1 : MonoidAlgebra ℤ (Equiv.Perm α)) *
        (single (Equiv.swap a c) 1 + single (Equiv.swap b c) 1 - single (Equiv.swap a b) 1) = 2 ∧
      (single (Equiv.swap a c) 1 + single (Equiv.swap b c) 1 - single (Equiv.swap a b) 1 :
          MonoidAlgebra ℤ (Equiv.Perm α)) *
        (single (Equiv.swap a c) 1 + single (Equiv.swap b c) 1) = 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := swap_relations hab hac hbc
  simp only [mul_sub, sub_mul, add_mul, mul_add, single_mul_single, Equiv.swap_mul_self,
    h1, h2, h3, h4, mul_one]
  have two : (2 : MonoidAlgebra ℤ (Equiv.Perm α)) = single 1 1 + single 1 1 := by
    rw [ofNat_def, ← single_add]; rfl
  rw [two]
  constructor <;> abel

/-- The Jucys–Murphy element `X₃ = (1 3) + (2 3)` in `ℤ[Sₙ]`, `n ≥ 3`. -/
noncomputable def X3 (n : ℕ) (hn : 3 ≤ n) : MonoidAlgebra ℤ (Equiv.Perm (Fin n)) :=
  single (Equiv.swap ⟨0, by omega⟩ ⟨2, by omega⟩) 1 +
    single (Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩) 1

/-- The transposition `(1 2)` in `ℤ[Sₙ]`, `n ≥ 3`. -/
noncomputable def T12 (n : ℕ) (hn : 3 ≤ n) : MonoidAlgebra ℤ (Equiv.Perm (Fin n)) :=
  single (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩) 1

/-- In `ℤ[Sₙ]`, `X₃ (X₃ - (1 2)) = 2 = (X₃ - (1 2)) X₃`. -/
theorem group_ring_identity (n : ℕ) (hn : 3 ≤ n) :
    X3 n hn * (X3 n hn - T12 n hn) = 2 ∧ (X3 n hn - T12 n hn) * X3 n hn = 2 :=
  swap_identity (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])

end StanleySmithForms
