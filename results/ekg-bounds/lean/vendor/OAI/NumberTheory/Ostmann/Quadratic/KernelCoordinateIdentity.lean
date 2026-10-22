import Mathlib
import OAI.NumberTheory.Ostmann.Characters.FiniteKernelCoordinates
import OAI.NumberTheory.Ostmann.Supply.CenteredProjectionPairing
import OAI.NumberTheory.Ostmann.Supply.CenteredSupportProjection

namespace OAI

/-! # Exact identification of the centered-coordinate kernel matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem centeredSupportProjection_pairing_range {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (f g : ZMod p → ℂ) :
    (∑ x, conj (centeredSupportProjection S f x) * centeredSupportProjection S g x) =
      ∑ x, conj (centeredSupportProjection S f x) * g x := by
  rw [centeredSupportProjection_pairing, centeredSupportProjection_idempotent]

/- The four blocks really represent `k(a-b)` on the centered coordinates of
the two residue points. This is the identity used before tensoring. -/
end Ostmann

end OAI
