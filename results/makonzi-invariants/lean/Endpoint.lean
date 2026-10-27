import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/- The quotient codomain is the arrow coordinate ring; the invariant subring's
inclusion is injective, so its kernel is the same as this map's kernel.
Proposition 5.1 supplies generation in the invariant subring separately. -/
namespace Makonzi
open scoped BigOperators
set_option linter.unusedVariables false

abbrev Edge (p : Fin 3 → ℕ) := (i : Fin 3) × Fin (p i)
abbrev Arrow (p : Fin 3 → ℕ) := Bool × Edge p
abbrev SourceVar (p : Fin 3 → ℕ) := Fin 3 ⊕ Edge p
abbrev SourceRing (p : Fin 3 → ℕ) := MvPolynomial (SourceVar p) ℂ
abbrev ArrowRing (p : Fin 3 → ℕ) := MvPolynomial (Arrow p) ℂ

noncomputable def D (p : Fin 3 → ℕ) (i : Fin 3) : ArrowRing p :=
  ∏ j : Fin (p i), MvPolynomial.X (false, ⟨i, j⟩)
noncomputable def U (p : Fin 3 → ℕ) (i : Fin 3) : ArrowRing p :=
  ∏ j : Fin (p i), MvPolynomial.X (true, ⟨i, j⟩)
noncomputable def V (p : Fin 3 → ℕ) (i : Fin 3) : SourceRing p :=
  ∏ j : Fin (p i), MvPolynomial.X (Sum.inr ⟨i, j⟩)
noncomputable def W (p : Fin 3 → ℕ) (i : Fin 3) : SourceRing p :=
  MvPolynomial.X (Sum.inl i)
noncomputable def canonicalIdeal (p : Fin 3 → ℕ) : Ideal (ArrowRing p) :=
  Ideal.span {D p 0 - D p 1 + D p 2}

noncomputable def arrowImage (p : Fin 3 → ℕ) : SourceVar p → ArrowRing p
  | Sum.inl i => if i = 0 then D p 0 * U p 1
      else if i = 1 then D p 1 * U p 0 else -(D p 1 * U p 2)
  | Sum.inr e => MvPolynomial.X (false, e) * MvPolynomial.X (true, e)

noncomputable def arrowEval (p : Fin 3 → ℕ) : SourceRing p →+* ArrowRing p :=
  MvPolynomial.eval₂Hom MvPolynomial.C (arrowImage p)

noncomputable def phi (p : Fin 3 → ℕ) :
    SourceRing p →+* ArrowRing p ⧸ canonicalIdeal p :=
  (Ideal.Quotient.mk (canonicalIdeal p)).comp (arrowEval p)

noncomputable def minorIdeal (p : Fin 3 → ℕ) : Ideal (SourceRing p) :=
  Ideal.span {W p 1 * (W p 2 + V p 2) - V p 0 * W p 2,
              W p 1 * W p 0 - V p 0 * V p 1,
              W p 2 * W p 0 - (W p 2 + V p 2) * V p 1}

/-- The intended, corrected all-arm Conjecture 5.2, not a finite tuple or
    an implication assuming primeness, flatness, or the desired kernel. -/
def Endpoint : Prop :=
  ∀ p : Fin 3 → ℕ, (∀ i, 2 ≤ p i) → RingHom.ker (phi p) = minorIdeal p

section CriticalPairs
variable {R : Type*} [CommRing R]

def f12 (x y z a b c : R) : R := x*y-a*b
def f13 (x y z a b c : R) : R := x*z-b*z-b*c
def f23 (x y z a b c : R) : R := y*z-a*z+c*y

/- Complete critical-pair identities for leading monomials xy,xz,yz.
These are checked algebraic lemmas only, not a confluence theorem. -/
theorem pair_01 (x y z a b c : R) :
    z * f12 x y z a b c - y * f13 x y z a b c =
    b * f23 x y z a b c := by
  unfold f12 f13 f23
  ring

theorem pair_02 (x y z a b c : R) :
    z * f12 x y z a b c - x * f23 x y z a b c =
    a * f13 x y z a b c - c * f12 x y z a b c := by
  unfold f12 f13 f23
  ring

theorem pair_12 (x y z a b c : R) :
    y * f13 x y z a b c - x * f23 x y z a b c =
    a * f13 x y z a b c - c * f12 x y z a b c - b * f23 x y z a b c := by
  unfold f12 f13 f23
  ring
end CriticalPairs

#check Endpoint
#print axioms pair_01
#print axioms pair_02
#print axioms pair_12
end Makonzi
