import Endpoint
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Localization.FractionRing

namespace Makonzi
open scoped BigOperators

abbrev CoeffRing (p : Fin 3 → ℕ) := MvPolynomial (Edge p) ℂ
abbrev CoeffField (p : Fin 3 → ℕ) := FractionRing (CoeffRing p)
abbrev RationalField (p : Fin 3 → ℕ) := RatFunc (CoeffField p)

noncomputable def coeffEmbed (p : Fin 3 → ℕ) : CoeffRing p →+* SourceRing p :=
  (MvPolynomial.rename Sum.inr).toRingHom

/-- One coefficient-polynomial constant and three finite positive-power sums.
The exponent bound is existential in the uniform theorem, never fixed. -/
noncomputable def normalForm (p : Fin 3 → ℕ) (N : ℕ)
    (r : CoeffRing p) (a b c : Fin N → CoeffRing p) : SourceRing p :=
  coeffEmbed p r +
    (∑ k : Fin N, coeffEmbed p (a k) * W p 0 ^ (k.val + 1)) +
    (∑ k : Fin N, coeffEmbed p (b k) * W p 1 ^ (k.val + 1)) +
    (∑ k : Fin N, coeffEmbed p (c k) * W p 2 ^ (k.val + 1))

noncomputable def coeffToRational (p : Fin 3 → ℕ) :
    CoeffRing p →+* RationalField p :=
  (algebraMap (CoeffField p) (RationalField p)).comp
    (algebraMap (CoeffRing p) (CoeffField p))

noncomputable def armCoeff (p : Fin 3 → ℕ) (i : Fin 3) : CoeffRing p :=
  ∏ j : Fin (p i), MvPolynomial.X (⟨i, j⟩ : Edge p)

end Makonzi
