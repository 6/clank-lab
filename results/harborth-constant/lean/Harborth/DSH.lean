import Mathlib
import Harborth.DSHAux

/-! Dias da Silva–Hamidoune theorem in `ZMod p`.

Proof by the polynomial method of Alon–Nathanson–Ruzsa; see `Harborth/DSHAux.lean`. -/

namespace Harborth

/-- Dias da Silva–Hamidoune: the sums of `h`-element subsets of `A ⊆ ZMod p` take at least
`min p (h * (|A| - h) + 1)` values. -/
theorem dsh {p : ℕ} [Fact p.Prime] (A : Finset (ZMod p)) (h : ℕ) (hh : h ≤ A.card) :
    min p (h * (A.card - h) + 1) ≤
      ((A.powersetCard h).image (fun B => ∑ x ∈ B, x)).card := by
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨t, hinj, hlt, hsum⟩ := DSHAux.exists_exponents h A.card
    (min (p - 1) (h * (A.card - h))) hh (min_le_right _ _)
  have := DSHAux.core A h t hinj hlt _ hsum (by omega)
  omega

end Harborth
