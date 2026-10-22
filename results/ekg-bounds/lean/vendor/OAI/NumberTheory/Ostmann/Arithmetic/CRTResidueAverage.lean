import Mathlib

namespace OAI

/-! # Exact independent residue averages from the Chinese remainder theorem -/

namespace Ostmann

open scoped BigOperators

/-- CRT on the actual unit residue classes, including prime-square moduli. -/
noncomputable def crtUnitEquiv {I : Type*} [Fintype I] (a : I → ℕ)
    (hc : Pairwise (fun i j => (a i).Coprime (a j))) :
    (ZMod (∏ i, a i))ˣ ≃* (∀ i, (ZMod (a i))ˣ) :=
  (Units.mapEquiv (ZMod.prodEquivPi a hc).toMulEquiv).trans MulEquiv.piUnits

end Ostmann

end OAI
