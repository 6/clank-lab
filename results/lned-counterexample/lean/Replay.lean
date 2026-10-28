import Claim
import RootOne

example : LNEDPilot.ENDPOINT := LNEDPilot.endpoint_proved
example : ¬ LNEDPilot.TwoSidedMathieu LNEDPilot.V := LNEDPilot.notMathieu_V
example : ¬ LNEDPilot.rootOneENDPOINT := LNEDPilot.rootOne_altered_false

open Polynomial
example :
    ∃ (φ : ℚ[X] →ₐ[ℚ] ℚ[X]) (D : ℚ[X] →ₗ[ℚ] ℚ[X]) (J : Ideal ℚ[X]),
      (∀ h : ℚ[X], φ h = h.comp (X + 1)) ∧
      (∀ h : ℚ[X], D h = h - φ h) ∧
      J = Ideal.span {(X : ℚ[X]) * (X - C (1 / 2 : ℚ))} ∧
      (∀ h : ℚ[X], ∃ N : ℕ, 0 < N ∧ ((D : ℚ[X] → ℚ[X])^[N]) h = 0) ∧
      (∀ h k : ℚ[X], D (h * k) = D h * k + h * D k - D h * D k) ∧
      ¬ LNEDPilot.TwoSidedMathieu ((fun h : ℚ[X] => D h) '' (J : Set ℚ[X])) :=
  LNEDPilot.exists_LNED_ideal_counterexample

#print axioms LNEDPilot.notMathieu_V
#print axioms LNEDPilot.exists_LNED_ideal_counterexample
