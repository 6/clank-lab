import Rescale

namespace LNEDExtension
open Polynomial
variable {R : Type*} [CommRing R] [IsDomain R] [Algebra ℚ R] [CharZero R]

noncomputable def shiftAlg (c : R) : R[X] →ₐ[R] R[X] := Polynomial.aeval (X + C c)

noncomputable def diffLinear (c : R) : R[X] →ₗ[R] R[X] :=
  LinearMap.id - (shiftAlg c).toLinearMap

lemma shiftAlg_apply (c : R) (p : R[X]) : shiftAlg c p = shift c p := rfl
lemma diffLinear_apply (c : R) (p : R[X]) : diffLinear c p = diff c p := rfl

variable {K : Type*} [Field K] [CharZero K]

lemma ideal_field_eq (c : K) :
    ideal c = Ideal.span {(X : K[X]) * (X - C (c / 2))} := by
  simp only [ideal, half_eq, div_eq_mul_inv, one_mul]

/-- Full literal field/shift extension, with actual algebra/linear maps and ideal.
The all-power statements use a=X² and b=X. -/
theorem field_shift_counterexample (c : K) (hc : c ≠ 0) :
    ∃ (φ : K[X] →ₐ[K] K[X]) (D : K[X] →ₗ[K] K[X]) (J : Ideal K[X]),
      (∀ p : K[X], φ p = p.comp (X + C c)) ∧
      (∀ p : K[X], D p = p - φ p) ∧
      J = Ideal.span {(X : K[X]) * (X - C (c / 2))} ∧
      (∀ p : K[X], ∃ N : ℕ, 0 < N ∧ ((D : K[X] → K[X])^[N]) p = 0) ∧
      (∀ p q : K[X], D (p * q) = D p * q + p * D q - D p * D q) ∧
      (∀ m : ℕ, 1 ≤ m → (X ^ 2 : K[X]) ^ m ∈ D '' (J : Set K[X])) ∧
      (∀ m : ℕ, 1 ≤ m → (X : K[X]) * (X ^ 2 : K[X]) ^ m ∉ D '' (J : Set K[X])) ∧
      ¬ Mathieu (D '' (J : Set K[X])) := by
  obtain ⟨hLN, hE, hev, hod, hM⟩ := nonzero_shift_endpoint c hc
  exact ⟨shiftAlg c, diffLinear c, ideal c, fun _ => rfl, fun _ => rfl,
    ideal_field_eq c, hLN, hE, hev, hod, hM⟩

/-- Unit-shift specialization for every characteristic-zero field. -/
theorem field_unit_counterexample :
    ∃ (φ : K[X] →ₐ[K] K[X]) (D : K[X] →ₗ[K] K[X]) (J : Ideal K[X]),
      (∀ p : K[X], φ p = p.comp (X + 1)) ∧
      (∀ p : K[X], D p = p - φ p) ∧
      J = Ideal.span {(X : K[X]) * (X - C (1 / 2 : K))} ∧
      (∀ p : K[X], ∃ N : ℕ, 0 < N ∧ ((D : K[X] → K[X])^[N]) p = 0) ∧
      (∀ p q : K[X], D (p * q) = D p * q + p * D q - D p * D q) ∧
      (∀ m : ℕ, 1 ≤ m → (X ^ 2 : K[X]) ^ m ∈ D '' (J : Set K[X])) ∧
      (∀ m : ℕ, 1 ≤ m → (X : K[X]) * (X ^ 2 : K[X]) ^ m ∉ D '' (J : Set K[X])) ∧
      ¬ Mathieu (D '' (J : Set K[X])) := by
  simpa only [C_1] using field_shift_counterexample (1 : K) one_ne_zero

#print axioms field_shift_counterexample
#print axioms field_unit_counterexample
end LNEDExtension
