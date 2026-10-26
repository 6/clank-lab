import FullProof
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Definition checks and the complete formal statement, built by default. -/

open Finset

namespace DonkinChecks

example (p : ℕ) : Donkin.productState p 0 = p := rfl
example (p k : ℕ) : Donkin.productState p (k + 1) =
    Donkin.productState p k * (Donkin.productState p k + 1).minFac := rfl
example (p : ℕ) : Donkin.term p 0 = p := rfl
example (p k : ℕ) : Donkin.term p (k + 1) =
    (Donkin.productState p k + 1).minFac := rfl
example : Donkin.ArbitraryDelay =
    (∀ n : ℕ, 0 < n → ∃ p : ℕ, Nat.Prime p ∧
      ∀ j : ℕ, j < n → Donkin.term p j ≠ 3) := rfl

-- The recursion is the literal product-plus-one recurrence.
theorem product_eq (p : ℕ) : ∀ k,
    Donkin.productState p k = ∏ i ∈ range (k + 1), Donkin.term p i
  | 0 => by simp [Donkin.productState, Donkin.term]
  | k + 1 => by
      rw [prod_range_succ, ← product_eq p k]
      rfl

theorem recurrence (p k : ℕ) :
    Donkin.term p (k + 1) =
      (1 + ∏ i ∈ range (k + 1), Donkin.term p i).minFac := by
  rw [← product_eq, Nat.add_comm 1]
  rfl

example (m : ℕ) (h : 2 ≤ m) :
    m.minFac.Prime ∧ m.minFac ∣ m ∧
      ∀ q : ℕ, q.Prime → q ∣ m → m.minFac ≤ q :=
  ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd m,
    fun _ hq hd => Nat.minFac_le_of_dvd hq.two_le hd⟩

-- The seed is the first term in each of these checks.
example : [Donkin.term 5 0, Donkin.term 5 1, Donkin.term 5 2, Donkin.term 5 3] =
    [5, 2, 11, 3] := by norm_num [Donkin.term, Donkin.productState]
example : [Donkin.term 2 0, Donkin.term 2 1, Donkin.term 2 2] =
    [2, 3, 7] := by norm_num [Donkin.term, Donkin.productState]
example : [Donkin.term 7 0, Donkin.term 7 1, Donkin.term 7 2,
    Donkin.term 7 3, Donkin.term 7 4, Donkin.term 7 5] =
    [7, 2, 3, 43, 13, 53] := by norm_num [Donkin.term, Donkin.productState]

example : ∀ n : ℕ, 0 < n → ∃ p : ℕ, Nat.Prime p ∧
    ∀ j : ℕ, j < n → Donkin.term p j ≠ 3 :=
  Donkin.arbitraryDelay

-- The zero-length case is vacuous; no uniform infinite-avoidance claim is made.
example : ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧
    ∀ j : ℕ, j < n → Donkin.term p j ≠ 3 := by
  intro n
  by_cases hn : n = 0
  · subst n
    exact ⟨2, Nat.prime_two, fun j hj => by omega⟩
  · exact Donkin.arbitraryDelay n (Nat.pos_of_ne_zero hn)

end DonkinChecks

/-- info: 'Donkin.big_prime_free_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Donkin.big_prime_free_residue

/-- info: 'Donkin.affine_avoidance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Donkin.affine_avoidance

/-- info: 'Donkin.small_prime_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Donkin.small_prime_residue

/-- info: 'Donkin.least_factor_from_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Donkin.least_factor_from_local

/-- info: 'Donkin.uniform_local_compatibility' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Donkin.uniform_local_compatibility

/-- info: 'Donkin.auxiliary_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Donkin.auxiliary_prime

/-- info: 'Donkin.prime_seed_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Donkin.prime_seed_lift

/-- info: 'Donkin.finite_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Donkin.finite_lift

/-- info: 'Donkin.tail_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Donkin.tail_exists

/-- info: 'Donkin.arbitraryDelay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Donkin.arbitraryDelay

