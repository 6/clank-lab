import Main

/-! The three theorems restated with the definition unfolded, their axioms, and small
examples of the definition. -/

open Harborth

/-- Theorem 1, upper bound: for every prime `p ≥ 11`, every set of `2p - 1` elements of
`C_p ⊕ C_p` contains `p` distinct elements whose sum is zero. -/
example : ∀ (p : ℕ) [Fact p.Prime], 11 ≤ p → ∀ S : Finset (ZMod p × ZMod p),
    S.card = 2 * p - 1 → ∃ T ⊆ S, T.card = p ∧ ∑ x ∈ T, x = 0 :=
  fun p _ hp S hS => upper p hp S hS

/-- Theorem 1, lower bound: for every odd prime `p`, some set of `2p - 2` elements has no
`p` distinct elements whose sum is zero. -/
example : ∀ (p : ℕ) [Fact p.Prime], 3 ≤ p → ∃ S : Finset (ZMod p × ZMod p),
    S.card = 2 * p - 2 ∧ ¬ ∃ T ⊆ S, T.card = p ∧ ∑ x ∈ T, x = 0 :=
  fun p _ hp => lower p hp

/-- Theorem 1: the Harborth constant of `C_p ⊕ C_p` is `2p - 1` for every prime `p ≥ 11`. -/
example : ∀ (p : ℕ) [Fact p.Prime], 11 ≤ p →
    sInf {k : ℕ | ∀ S : Finset (ZMod p × ZMod p), S.card = k →
      ∃ T ⊆ S, T.card = p ∧ ∑ x ∈ T, x = 0} = 2 * p - 1 :=
  fun p _ hp => harborth_constant p hp

/-- info: 'Harborth.upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Harborth.upper

/-- info: 'Harborth.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Harborth.lower

/-- info: 'Harborth.harborth_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Harborth.harborth_constant

/-- A full line of `C_3 ⊕ C_3`, three distinct points, sums to zero. -/
example : HasZeroSumPSubset 3 ({(0, 0), (1, 0), (2, 0)} : Finset (ZMod 3 × ZMod 3)) :=
  ⟨_, subset_rfl, by decide, by decide⟩

/-- The lower-bound set at `p = 3`, `{0, 1} × {1, 2}`, has no three distinct points
summing to zero. -/
example : ¬ HasZeroSumPSubset 3 ({(0, 1), (0, 2), (1, 1), (1, 2)} : Finset (ZMod 3 × ZMod 3)) := by
  rintro ⟨T, hT, hc, hs⟩
  have key : ∀ U ∈ ({(0, 1), (0, 2), (1, 1), (1, 2)} : Finset (ZMod 3 × ZMod 3)).powerset,
      ¬ (U.card = 3 ∧ ∑ x ∈ U, x = 0) := by decide +kernel
  exact key T (Finset.mem_powerset.2 hT) ⟨hc, hs⟩

/-- The theorem at `p = 11`: `g(C_11 ⊕ C_11) = 21`. -/
example : sInf {k : ℕ | ∀ S : Finset (ZMod 11 × ZMod 11), S.card = k →
    HasZeroSumPSubset 11 S} = 21 :=
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  harborth_constant 11 le_rfl
