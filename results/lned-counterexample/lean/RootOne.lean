import D5

namespace LNEDPilot
open Polynomial

def rootOneI : Set ℚ[X] := {h | ∃ q : ℚ[X], h = X * (X - 1) * q}
def rootOneV : Set ℚ[X] := delta '' rootOneI

def rootOneENDPOINT : Prop :=
  (∀ h : ℚ[X], ∃ N : ℕ, (delta^[N]) h = 0) ∧
  (∀ h k : ℚ[X], delta (h * k) = delta h * k + h * delta k - delta h * delta k) ∧
  (∀ m : ℕ, 1 ≤ m → (X ^ 2 : ℚ[X]) ^ m ∈ rootOneV) ∧
  (∀ m : ℕ, 1 ≤ m → (X : ℚ[X]) * (X ^ 2 : ℚ[X]) ^ m ∉ rootOneV)

lemma rootOne_witness : (X : ℚ[X]) * (X ^ 2 : ℚ[X]) ^ 1 ∈ rootOneV := by
  refine ⟨X * (X - 1) * (C (-1 / 4 : ℚ) * X * (X - 1)),
    ⟨C (-1 / 4 : ℚ) * X * (X - 1), rfl⟩, ?_⟩
  apply Polynomial.funext
  intro q
  simp only [delta, phi, eval_comp, eval_mul, eval_sub, eval_C, eval_X,
    eval_one, eval_add, eval_pow]
  ring

lemma rootOne_altered_false : ¬ rootOneENDPOINT := by
  intro h
  exact h.2.2.2 1 (by omega) rootOne_witness

#print axioms rootOne_altered_false
end LNEDPilot
