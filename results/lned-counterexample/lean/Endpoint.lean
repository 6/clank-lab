import Mathlib.NumberTheory.ZetaValues

/- The rational polynomial-image endpoint. -/
namespace LNEDPilot
open Polynomial

noncomputable def phi (h : ℚ[X]) : ℚ[X] := h.comp (X + 1)
noncomputable def delta (h : ℚ[X]) : ℚ[X] := h - phi h
def I : Set ℚ[X] := {h | ∃ q : ℚ[X], h = X * (X - C (1 / 2 : ℚ)) * q}
def V : Set ℚ[X] := delta '' I

/-- The actual polynomial image, with local nilpotence and both infinite quantifiers. -/
def ENDPOINT : Prop :=
  (∀ h : ℚ[X], ∃ N : ℕ, (delta^[N]) h = 0) ∧
  (∀ h k : ℚ[X], delta (h * k) = delta h * k + h * delta k - delta h * delta k) ∧
  (∀ m : ℕ, 1 ≤ m → (X ^ 2 : ℚ[X]) ^ m ∈ V) ∧
  (∀ m : ℕ, 1 ≤ m → (X : ℚ[X]) * (X ^ 2 : ℚ[X]) ^ m ∉ V)
end LNEDPilot
