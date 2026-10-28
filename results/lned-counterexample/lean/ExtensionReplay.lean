import ChosenVariable

open LNEDExtension

example (K : Type*) [Field K] [CharZero K] : UnitEndpoint K := field_endpoint K
example (K : Type*) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) : ShiftEndpoint c :=
  nonzero_shift_endpoint c hc
example (K : Type*) [Field K] [CharZero K] : Mathieu (image (0 : K)) := zero_shift_mathieu
example (K : Type*) [Field K] [CharZero K] (τ : Type*) (v : τ) : ChosenEndpoint (K := K) v :=
  chosen_variable_endpoint v
example (K : Type*) [Field K] [CharZero K] (n : ℕ) (hn : 1 ≤ n) :
    ChosenEndpoint (K := K) (⟨0, hn⟩ : Fin n) := finite_variable_endpoint n hn

#print axioms LNEDExtension.monomial_image_iff
#print axioms LNEDExtension.field_shift_counterexample
#print axioms LNEDExtension.field_unit_counterexample
#print axioms LNEDExtension.zero_shift_image
#print axioms LNEDExtension.zero_shift_mathieu
#print axioms LNEDExtension.zero_shift_endpoint_false
#print axioms LNEDExtension.chosen_variable_counterexample
#print axioms LNEDExtension.finite_variable_endpoint
