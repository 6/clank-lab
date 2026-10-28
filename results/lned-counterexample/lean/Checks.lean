import Replay
import ExtensionReplay
import BetaReplay
import NegativeHalf
import ScopeControl

/-! Exact endpoint types and definition checks, checked by the default Lake build. -/
open Polynomial
open scoped BigOperators

namespace LNEDPilot

example :
    ∃ (φ : ℚ[X] →ₐ[ℚ] ℚ[X]) (D : ℚ[X] →ₗ[ℚ] ℚ[X]) (J : Ideal ℚ[X]),
      (∀ h : ℚ[X], φ h = h.comp (X + 1)) ∧
      (∀ h : ℚ[X], D h = h - φ h) ∧
      J = Ideal.span {(X : ℚ[X]) * (X - C (1 / 2 : ℚ))} ∧
      (∀ h : ℚ[X], ∃ N : ℕ, 0 < N ∧ ((D : ℚ[X] → ℚ[X])^[N]) h = 0) ∧
      (∀ h k : ℚ[X], D (h * k) = D h * k + h * D k - D h * D k) ∧
      ¬ TwoSidedMathieu ((fun h : ℚ[X] => D h) '' (J : Set ℚ[X])):= exists_LNED_ideal_counterexample

example : ENDPOINT:= endpoint_proved

end LNEDPilot

namespace LNEDExtension
variable {K : Type*} [Field K] [CharZero K] {τ : Type*}

example (c : K) (hc : c ≠ 0) :
    ∃ (φ : K[X] →ₐ[K] K[X]) (D : K[X] →ₗ[K] K[X]) (J : Ideal K[X]),
      (∀ p : K[X], φ p = p.comp (X + C c)) ∧
      (∀ p : K[X], D p = p - φ p) ∧
      J = Ideal.span {(X : K[X]) * (X - C (c / 2))} ∧
      (∀ p : K[X], ∃ N : ℕ, 0 < N ∧ ((D : K[X] → K[X])^[N]) p = 0) ∧
      (∀ p q : K[X], D (p * q) = D p * q + p * D q - D p * D q) ∧
      (∀ m : ℕ, 1 ≤ m → (X ^ 2 : K[X]) ^ m ∈ D '' (J : Set K[X])) ∧
      (∀ m : ℕ, 1 ≤ m → (X : K[X]) * (X ^ 2 : K[X]) ^ m ∉ D '' (J : Set K[X])) ∧
      ¬ Mathieu (D '' (J : Set K[X])):= field_shift_counterexample c hc

example :
    ∃ (φ : K[X] →ₐ[K] K[X]) (D : K[X] →ₗ[K] K[X]) (J : Ideal K[X]),
      (∀ p : K[X], φ p = p.comp (X + 1)) ∧
      (∀ p : K[X], D p = p - φ p) ∧
      J = Ideal.span {(X : K[X]) * (X - C (1 / 2 : K))} ∧
      (∀ p : K[X], ∃ N : ℕ, 0 < N ∧ ((D : K[X] → K[X])^[N]) p = 0) ∧
      (∀ p q : K[X], D (p * q) = D p * q + p * D q - D p * D q) ∧
      (∀ m : ℕ, 1 ≤ m → (X ^ 2 : K[X]) ^ m ∈ D '' (J : Set K[X])) ∧
      (∀ m : ℕ, 1 ≤ m → (X : K[X]) * (X ^ 2 : K[X]) ^ m ∉ D '' (J : Set K[X])) ∧
      ¬ Mathieu (D '' (J : Set K[X])):= field_unit_counterexample

example (v : τ) :
    ∃ (φ : MvPolynomial τ K →ₐ[K] MvPolynomial τ K)
      (D : MvPolynomial τ K →ₗ[K] MvPolynomial τ K) (J : Ideal (MvPolynomial τ K)),
      φ (MvPolynomial.X v) = MvPolynomial.X v + 1 ∧
      (∀ i : τ, i ≠ v → φ (MvPolynomial.X i) = MvPolynomial.X i) ∧
      (∀ p : MvPolynomial τ K, D p = p - φ p) ∧
      J = Ideal.span {MvPolynomial.X v * (MvPolynomial.X v - MvPolynomial.C (1 / 2 : K))} ∧
      (∀ p : MvPolynomial τ K, ∃ N : ℕ, 0 < N ∧ ((D : _ → _)^[N]) p = 0) ∧
      (∀ p q : MvPolynomial τ K, D (p * q) = D p * q + p * D q - D p * D q) ∧
      (∀ m : ℕ, 1 ≤ m → ((MvPolynomial.X v) ^ 2 : MvPolynomial τ K) ^ m ∈ D '' (J : Set _)) ∧
      (∀ m : ℕ, 1 ≤ m → (MvPolynomial.X v : MvPolynomial τ K) *
        ((MvPolynomial.X v) ^ 2 : MvPolynomial τ K) ^ m ∉ D '' (J : Set _)) ∧
      ¬ ChosenMathieu (D '' (J : Set _)):= chosen_variable_counterexample v

example (v : τ) : ChosenEndpoint (K := K) v:= chosen_variable_endpoint v

example (n : ℕ) (hn : 1 ≤ n) :
    ChosenEndpoint (K := K) (⟨0, hn⟩ : Fin n):= finite_variable_endpoint n hn

example :
    ∃ (φ : K[X] →ₐ[K] K[X]) (D : K[X] →ₗ[K] K[X]) (J : Ideal K[X]),
      (∀ p : K[X], φ p = p.comp (X + 1)) ∧
      (∀ p : K[X], D p = p - φ p) ∧
      J = Ideal.span {(X : K[X]) * (X - C (-1 / 2 : K))} ∧
      (∀ p : K[X], ∃ N : ℕ, 0 < N ∧ ((D : K[X] → K[X])^[N]) p = 0) ∧
      (∀ p q : K[X], D (p * q) = D p * q + p * D q - D p * D q) ∧
      (∀ m : ℕ, 1 ≤ m → ((X + C (1 / 2 : K)) ^ 2) ^ m ∈ D '' (J : Set K[X])) ∧
      (∀ m : ℕ, 1 ≤ m → (X + C (1 / 2 : K)) * ((X + C (1 / 2 : K)) ^ 2) ^ m ∉ D '' (J : Set K[X])) ∧
      ¬ Mathieu (D '' (J : Set K[X])):= negativeHalf_counterexample

example : NegativeHalfEndpoint K:= negativeHalf_endpoint

example (c : K) (hc : c ≠ 0) : ShiftEndpoint c:= nonzero_shift_endpoint c hc

example : image (0 : K) = {0}:= zero_shift_image

example : Mathieu (image (0 : K)):= zero_shift_mathieu

example : ¬ ShiftEndpoint (0 : K):= zero_shift_endpoint_false

end LNEDExtension

open LNEDPilot LNEDBeta

example : ∀ r : ℕ,
    ¬ TwoSidedMathieu (delta ''
      ((Ideal.span {(X : ℚ[X]) * (X - C ((r : ℚ) + 1 / 2))} : Ideal ℚ[X]) : Set ℚ[X])) ∧
    ¬ TwoSidedMathieu (delta ''
      ((Ideal.span {(X : ℚ[X]) * (X - C (-((r : ℚ) + 1 / 2)))} : Ideal ℚ[X]) : Set ℚ[X])):= signed_half_literal

example : ∀ N : ℕ, 0 < N →
    TwoSidedMathieu (delta ''
      ((Ideal.span {(X : ℚ[X]) * (X - C (N : ℚ))} : Ideal ℚ[X]) : Set ℚ[X])) ∧
    TwoSidedMathieu (delta ''
      ((Ideal.span {(X : ℚ[X]) * (X - C (-(N : ℚ)))} : Ideal ℚ[X]) : Set ℚ[X])):= signed_integer_literal

namespace LNEDBeta
open LNEDPilot

example : HalfWitnessEndpoint:= half_witness_all

example (r : ℕ) :
    (∀ m : ℕ, 1 ≤ m → (trans ((r : ℚ) + 1 / 2) (P r)) ^ m ∈
      VBeta (-((r : ℚ) + 1 / 2))) ∧
    (∀ m : ℕ, 1 ≤ m → (X + C ((r : ℚ) + 1 / 2)) *
      (trans ((r : ℚ) + 1 / 2) (P r)) ^ m ∉ VBeta (-((r : ℚ) + 1 / 2))):= negative_half_witness r

end LNEDBeta

namespace LNEDScope
open LNEDExtension
variable {K : Type*} [Field K] [CharZero K]

example :
    let V : Set K[X] := (fun f : K[X] => f - f.comp (X + 1)) ''
      ((Ideal.span {(X : K[X]) * (X - C (1 / 2 : K))} : Ideal K[X]) : Set K[X])
    (∀ J : Ideal K[X], (J : Set K[X]) ⊆ V → J = ⊥) ∧
    {a : K[X] | ∀ b : K[X], ∃ N : ℕ, ∀ m : ℕ, N ≤ m → b * a ^ m ∈ V} = {0}:= scope_literal

example : ScopeEndpoint K:= scope_endpoint

example (J : Ideal K[X])
    (hJ : (J : Set K[X]) ⊆ image (1 : K)) : J = ⊥:= no_nonzero_contained_ideal J hJ

example : StrongRadical (image (1 : K)) = {0}:= strong_radical_eq_zero

end LNEDScope

namespace LNEDPilot

example  : ENDPOINT  = ((∀ h : ℚ[X], ∃ N : ℕ, (delta^[N]) h = 0) ∧
  (∀ h k : ℚ[X], delta (h * k) = delta h * k + h * delta k - delta h * delta k) ∧
  (∀ m : ℕ, 1 ≤ m → (X ^ 2 : ℚ[X]) ^ m ∈ V) ∧
  (∀ m : ℕ, 1 ≤ m → (X : ℚ[X]) * (X ^ 2 : ℚ[X]) ^ m ∉ V)) := rfl

end LNEDPilot

namespace LNEDExtension
variable {R : Type*} [CommRing R] [IsDomain R] [Algebra ℚ R] [CharZero R]

example (R : Type*) [CommRing R] [IsDomain R] [Algebra ℚ R] [CharZero R] : UnitEndpoint R = ((∀ p : R[X], ∃ N : ℕ, 0 < N ∧ ((diff 1)^[N]) p = 0) ∧
  (∀ p q : R[X], diff 1 (p * q) = diff 1 p * q + p * diff 1 q - diff 1 p * diff 1 q) ∧
  (∀ m : ℕ, 1 ≤ m → (X ^ 2 : R[X]) ^ m ∈ image 1) ∧
  (∀ m : ℕ, 1 ≤ m → (X : R[X]) * (X ^ 2 : R[X]) ^ m ∉ image 1) ∧
  ¬ Mathieu (image (1 : R))) := rfl

example (c : R) : ShiftEndpoint c = ((∀ p : R[X], ∃ N : ℕ, 0 < N ∧ ((diff c)^[N]) p = 0) ∧
  (∀ p q : R[X], diff c (p * q) = diff c p * q + p * diff c q - diff c p * diff c q) ∧
  (∀ m : ℕ, 1 ≤ m → (X ^ 2 : R[X]) ^ m ∈ image c) ∧
  (∀ m : ℕ, 1 ≤ m → (X : R[X]) * (X ^ 2 : R[X]) ^ m ∉ image c) ∧
  ¬ Mathieu (image c)) := rfl

end LNEDExtension

namespace LNEDExtension
variable {K : Type*} [Field K] [CharZero K] {τ : Type*}

example (v : τ) : ChosenEndpoint (K := K) v = ((∀ p : MvPolynomial τ K, ∃ N : ℕ, 0 < N ∧ ((chosenDiff v)^[N]) p = 0) ∧
  (∀ p q : MvPolynomial τ K, chosenDiff v (p * q) =
    chosenDiff v p * q + p * chosenDiff v q - chosenDiff v p * chosenDiff v q) ∧
  (∀ m : ℕ, 1 ≤ m → ((MvPolynomial.X v) ^ 2 : MvPolynomial τ K) ^ m ∈ chosenImage v) ∧
  (∀ m : ℕ, 1 ≤ m → (MvPolynomial.X v : MvPolynomial τ K) *
    ((MvPolynomial.X v) ^ 2 : MvPolynomial τ K) ^ m ∉ chosenImage v) ∧
  ¬ ChosenMathieu (chosenImage v : Set (MvPolynomial τ K))) := rfl

end LNEDExtension

namespace LNEDBeta
open LNEDPilot

example  : HalfWitnessEndpoint  = (∀ r : ℕ,
  (∀ m : ℕ, 1 ≤ m → P r ^ m ∈ VBeta ((r : ℚ) + 1 / 2)) ∧
  (∀ m : ℕ, 1 ≤ m → X * P r ^ m ∉ VBeta ((r : ℚ) + 1 / 2))) := rfl

end LNEDBeta

namespace LNEDExtension

example (K : Type*) [Field K] [CharZero K] : NegativeHalfEndpoint K = ((∀ m : ℕ, 1 ≤ m → ((X + C (1 / 2 : K)) ^ 2) ^ m ∈ negativeHalfImage) ∧
  (∀ m : ℕ, 1 ≤ m → (X + C (1 / 2 : K)) * ((X + C (1 / 2 : K)) ^ 2) ^ m ∉ negativeHalfImage) ∧
  ¬ Mathieu (negativeHalfImage : Set K[X])) := rfl

end LNEDExtension

namespace LNEDScope
open LNEDExtension

example (K : Type*) [Field K] [CharZero K] : ScopeEndpoint K = ((∀ J : Ideal K[X], (J : Set K[X]) ⊆ image 1 → J = ⊥) ∧
  StrongRadical (image (1 : K)) = {0}) := rfl

end LNEDScope

-- Small checks of the actual operators and ideal generators.
example : LNEDPilot.delta (1 : ℚ[X]) = 0 := by
  simp [LNEDPilot.delta, LNEDPilot.phi]
example : LNEDExtension.diff (0 : ℚ) X = 0 := by
  simp [LNEDExtension.diff, LNEDExtension.shift]
example : LNEDBeta.P 0 = (X : ℚ[X]) ^ 2 := by
  simp [LNEDBeta.P]
example : LNEDBeta.IBeta (1 / 2) =
    Ideal.span {(X : ℚ[X]) * (X - C (1 / 2 : ℚ))} := rfl

/-! Each listed declaration must use exactly the three standard axioms. -/

/-- info: 'LNEDBeta.all_negative_half_not_mathieu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDBeta.all_negative_half_not_mathieu

/-- info: 'LNEDBeta.all_negative_integer_mathieu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDBeta.all_negative_integer_mathieu

/-- info: 'LNEDBeta.all_positive_half_not_mathieu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDBeta.all_positive_half_not_mathieu

/-- info: 'LNEDBeta.half_odd_moment_strict_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDBeta.half_odd_moment_strict_sign

/-- info: 'LNEDBeta.half_witness_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDBeta.half_witness_all

/-- info: 'LNEDBeta.mem_VBeta_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDBeta.mem_VBeta_iff

/-- info: 'LNEDBeta.negative_half_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDBeta.negative_half_witness

/-- info: 'LNEDBeta.positive_integer_mathieu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDBeta.positive_integer_mathieu

/-- info: 'LNEDExtension.chosenRename_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.chosenRename_ideal

/-- info: 'LNEDExtension.chosenRename_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.chosenRename_image

/-- info: 'LNEDExtension.chosenRename_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.chosenRename_shift

/-- info: 'LNEDExtension.chosen_variable_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.chosen_variable_counterexample

/-- info: 'LNEDExtension.chosen_variable_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.chosen_variable_endpoint

/-- info: 'LNEDExtension.field_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.field_endpoint

/-- info: 'LNEDExtension.field_shift_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.field_shift_counterexample

/-- info: 'LNEDExtension.field_unit_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.field_unit_counterexample

/-- info: 'LNEDExtension.finite_variable_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.finite_variable_endpoint

/-- info: 'LNEDExtension.monomial_image_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.monomial_image_iff

/-- info: 'LNEDExtension.multivariable_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.multivariable_endpoint

/-- info: 'LNEDExtension.negativeHalf_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.negativeHalf_counterexample

/-- info: 'LNEDExtension.negativeHalf_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.negativeHalf_endpoint

/-- info: 'LNEDExtension.nonzero_shift_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.nonzero_shift_endpoint

/-- info: 'LNEDExtension.translateHalf_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.translateHalf_diff

/-- info: 'LNEDExtension.translateHalf_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.translateHalf_ideal

/-- info: 'LNEDExtension.translateHalf_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.translateHalf_image

/-- info: 'LNEDExtension.unit_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.unit_endpoint

/-- info: 'LNEDExtension.univariate_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.univariate_ideal

/-- info: 'LNEDExtension.univariate_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.univariate_image

/-- info: 'LNEDExtension.univariate_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.univariate_shift

/-- info: 'LNEDExtension.zero_shift_endpoint_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.zero_shift_endpoint_false

/-- info: 'LNEDExtension.zero_shift_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.zero_shift_image

/-- info: 'LNEDExtension.zero_shift_mathieu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDExtension.zero_shift_mathieu

/-- info: 'LNEDPilot.bernoulli_half_gap_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDPilot.bernoulli_half_gap_all

/-- info: 'LNEDPilot.delta_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDPilot.delta_H

/-- info: 'LNEDPilot.delta_kernel_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDPilot.delta_kernel_constant

/-- info: 'LNEDPilot.delta_locally_nilpotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDPilot.delta_locally_nilpotent

/-- info: 'LNEDPilot.endpoint_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDPilot.endpoint_proved

/-- info: 'LNEDPilot.exists_LNED_ideal_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDPilot.exists_LNED_ideal_counterexample

/-- info: 'LNEDPilot.mem_I_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDPilot.mem_I_iff

/-- info: 'LNEDPilot.monomial_image_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDPilot.monomial_image_iff

/-- info: 'LNEDPilot.notMathieu_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDPilot.notMathieu_V

/-- info: 'LNEDPilot.rootOne_altered_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDPilot.rootOne_altered_false

/-- info: 'LNEDScope.F_halfshift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDScope.F_halfshift

/-- info: 'LNEDScope.F_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDScope.F_one

/-- info: 'LNEDScope.annihilator_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDScope.annihilator_eq_bot

/-- info: 'LNEDScope.beta_one_contains_nonzero_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDScope.beta_one_contains_nonzero_ideal

/-- info: 'LNEDScope.beta_one_image_eq_Xideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDScope.beta_one_image_eq_Xideal

/-- info: 'LNEDScope.beta_one_strong_radical_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDScope.beta_one_strong_radical_nonzero

/-- info: 'LNEDScope.mem_image_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDScope.mem_image_iff

/-- info: 'LNEDScope.no_nonzero_contained_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDScope.no_nonzero_contained_ideal

/-- info: 'LNEDScope.scope_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDScope.scope_endpoint

/-- info: 'LNEDScope.scope_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDScope.scope_literal

/-- info: 'LNEDScope.strong_radical_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LNEDScope.strong_radical_eq_zero

/-- info: 'signed_half_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signed_half_literal

/-- info: 'signed_integer_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signed_integer_literal
