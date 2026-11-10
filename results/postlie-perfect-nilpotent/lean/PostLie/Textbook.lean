import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace PostLie

attribute [local instance] LieRing.ofAssociativeRing

/-- Weibel, *An Introduction to Homological Algebra* (Cambridge, 1994),
Levi's Theorem 7.8.13: "If g is a finite-dimensional Lie algebra over a field
of characteristic zero, then there is a semisimple Lie subalgebra C of g
(called a Levi factor of g) such that g is isomorphic to the semidirect
product g = (rad g) ⋊ C." Weibel calls g semisimple if rad g = 0 (§7.8), and
by Weibel's Theorem 7.8.5 that means a finite product of simple Lie algebras,
which is Mathlib's `IsSemisimple`. Used in this form: if g is not solvable
then rad g ≠ g, so C ≅ g/(rad g) is nonzero. -/
axiom levi_nonzero_semisimple (k g : Type*) [Field k] [CharZero k]
    [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    (h : ¬ LieAlgebra.IsSolvable g) :
    ∃ s : LieSubalgebra k g, Nontrivial s ∧ LieAlgebra.IsSemisimple k s

/-- Weibel, *An Introduction to Homological Algebra* (Cambridge, 1994),
Corollary 7.8.10 (Whitehead's first lemma): "Let g be a semisimple Lie
algebra over a field of characteristic 0. If M is any finite-dimensional
g-module, then H^1(g, M) = 0. That is, every derivation from g into M is an
inner derivation." A derivation (Definition 7.4.3) is a linear D with
D([x,y]) = x(Dy) − y(Dx); the inner ones are D_m(x) = xm (Example 7.4.4).
The module is a Lie algebra representation into `Module.End`. -/
axiom whitehead_first (k s M : Type*) [Field k] [CharZero k]
    [LieRing s] [LieAlgebra k s] [FiniteDimensional k s]
    [LieAlgebra.IsSemisimple k s] [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] (ρ : s →ₗ⁅k⁆ Module.End k M) (c : s →ₗ[k] M)
    (hc : ∀ x y, c ⁅x, y⁆ = ρ x (c y) - ρ y (c x)) :
    ∃ m : M, ∀ x, c x = ρ x m

end PostLie
