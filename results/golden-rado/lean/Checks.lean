import Hopkins

/-! The main statements with their exact types, small instances, and the axioms they use. -/

open Hopkins

-- The definitions, unfolded.
example (N : ℕ) (c : ℕ → Bool) :
    Valid N c = (c 1 = false ∧ ∀ i : ℕ, 1 ≤ i → i + 1 ≤ N →
      ¬ (c i = true ∧ c (i + 1) = true)) := rfl
example (a b N : ℕ) (c : ℕ → Bool) :
    Mono a b N c = (∃ x y z : ℕ, 1 ≤ x ∧ x ≤ N ∧ 1 ≤ y ∧ y ≤ N ∧
      1 ≤ z ∧ z ≤ N ∧ a * x + b * y = z ∧ c x = c y ∧ c y = c z) := rfl
example (a b N : ℕ) : Forces a b N = ∀ c : ℕ → Bool, Valid N c → Mono a b N c := rfl
example (a b : ℕ) : ForcingSet a b = {N | 1 ≤ N ∧ Forces a b N} := rfl
example (a b : ℕ) : R0phi a b = sInf (ForcingSet a b) := rfl

-- The upper bound (for every a ≥ 1), the lower-bound coloring, and the formula.
example : ∀ a ell : ℕ, 1 ≤ a → 1 ≤ ell →
    Forces a (a * ell) (a ^ 2 * (ell + 1) ^ 2) := upper
example : ∀ a ell M : ℕ, 2 ≤ a → 1 ≤ ell → 1 ≤ M → M < a ^ 2 * (ell + 1) ^ 2 →
    Valid M (lowerColor a ell) ∧ ¬ Mono a (a * ell) M (lowerColor a ell) := lower
example : ∀ a ell : ℕ, 2 ≤ a → 1 ≤ ell →
    IsLeast (ForcingSet a (a * ell)) (a ^ 2 * (ell + 1) ^ 2) := formula_isLeast
example : ∀ a ell : ℕ, 2 ≤ a → 1 ≤ ell →
    R0phi a (a * ell) = a ^ 2 * (ell + 1) ^ 2 := formula

-- Instances: Hopkins's Theorem 2 at a = 2, and the first new case, a = 2 with b = 4.
example : R0phi 2 2 = 16 := by simpa using formula 2 1 (by norm_num) le_rfl
example : R0phi 2 4 = 36 := by simpa using formula 2 2 (by norm_num) (by norm_num)

-- At a = 1 the printed formula fails: R0phi 1 2 is 4, not (2 + 1) ^ 2 = 9.
example : R0phi 1 1 = 4 := control11
example : R0phi 1 2 = 4 := control12

-- Each theorem uses only Lean's standard axioms; the build fails if this output changes.
/-- info: 'Hopkins.upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hopkins.upper

/-- info: 'Hopkins.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hopkins.lower

/-- info: 'Hopkins.formula_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hopkins.formula_isLeast

/-- info: 'Hopkins.formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hopkins.formula

/-- info: 'Hopkins.control12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hopkins.control12
