import Claim

namespace LNEDExtension
open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [Algebra ℚ R] [CharZero R]

noncomputable def half : R := algebraMap ℚ R (1 / 2)
noncomputable def shift (c : R) (p : R[X]) : R[X] := p.comp (X + C c)
noncomputable def diff (c : R) (p : R[X]) : R[X] := p - shift c p
noncomputable def ideal (c : R) : Ideal R[X] :=
  Ideal.span {X * (X - C (c * half))}
noncomputable def image (c : R) : Set R[X] := diff c '' (ideal c : Set R[X])

def Mathieu (W : Set R[X]) : Prop :=
  ∀ a : R[X], (∀ m : ℕ, 1 ≤ m → a ^ m ∈ W) →
    ∀ b d : R[X], ∃ N : ℕ, ∀ m : ℕ, N ≤ m → b * a ^ m * d ∈ W

/-- Exact unit-shift endpoint, including actual image nonmembership. -/
def UnitEndpoint (R : Type*) [CommRing R] [IsDomain R] [Algebra ℚ R] [CharZero R] : Prop :=
  (∀ p : R[X], ∃ N : ℕ, 0 < N ∧ ((diff 1)^[N]) p = 0) ∧
  (∀ p q : R[X], diff 1 (p * q) = diff 1 p * q + p * diff 1 q - diff 1 p * diff 1 q) ∧
  (∀ m : ℕ, 1 ≤ m → (X ^ 2 : R[X]) ^ m ∈ image 1) ∧
  (∀ m : ℕ, 1 ≤ m → (X : R[X]) * (X ^ 2 : R[X]) ^ m ∉ image 1) ∧
  ¬ Mathieu (image (1 : R))

def ShiftEndpoint (c : R) : Prop :=
  (∀ p : R[X], ∃ N : ℕ, 0 < N ∧ ((diff c)^[N]) p = 0) ∧
  (∀ p q : R[X], diff c (p * q) = diff c p * q + p * diff c q - diff c p * diff c q) ∧
  (∀ m : ℕ, 1 ≤ m → (X ^ 2 : R[X]) ^ m ∈ image c) ∧
  (∀ m : ℕ, 1 ≤ m → (X : R[X]) * (X ^ 2 : R[X]) ^ m ∉ image c) ∧
  ¬ Mathieu (image c)

end LNEDExtension
