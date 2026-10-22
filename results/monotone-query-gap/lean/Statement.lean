import KS24

-- These type annotations pin both public endpoint statements.
example :
    KS24.Monotone ∧
    (∀ A : KS24.Alg, (∀ x < 32, KS24.Correct A 0 x) → 104 ≤ KS24.totalCost A) ∧
    (∃ A : KS24.Alg, (∀ x < 32, KS24.Correct A 0 x) ∧ KS24.totalCost A = 104) ∧
    (∃ P : List (Nat × Nat), KS24.IsPartition P ∧ KS24.Determines P ∧
      KS24.totalCodim P = 102) := KS24.answer

example : ∃ P : List (Nat × Nat), KS24.IsPartition P ∧ KS24.Determines P ∧
    ∀ A : KS24.Alg, (∀ x < 32, KS24.Correct A 0 x) →
      KS24.totalCodim P < KS24.totalCost A := KS24.gap
