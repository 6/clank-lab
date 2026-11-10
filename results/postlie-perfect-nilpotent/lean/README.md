# Lean development

Run `lake exe cache get` and then `lake build` in this directory. `lean-toolchain` selects Lean v4.34.0, and `lakefile.toml` pins Mathlib to commit `5ed2965256430c3649e86755f9576b54eca72435`. The default build checks the library `PostLie` and the file `PublicChecks.lean`. With the Mathlib cache, it takes about two minutes and under 3 GB of memory.

## Statements and correspondence

The definitions are in `PostLie/Definitions.lean`. The paper's two brackets on one space $V$ are two Lie algebras `g` and `n` over a field `k` with `[CharZero k]`, both finite-dimensional, together with a linear equivalence `e : g ≃ₗ[k] n`. The bracket of `n` read on `g` is `e.symm ⁅e y, e z⁆`.

```lean
structure Product (e : g ≃ₗ[k] n) where
  mul : g →ₗ[k] g →ₗ[k] g
  skew : ∀ x y, mul x y - mul y x = ⁅x, y⁆ - e.symm ⁅e x, e y⁆
  left_lie : ∀ x y z, mul ⁅x, y⁆ z = mul x (mul y z) - mul y (mul x z)
  derivation : ∀ x y z, mul x (e.symm ⁅e y, e z⁆) =
    e.symm ⁅e (mul x y), e z⁆ + e.symm ⁅e y, e (mul x z)⁆

def right {e : g ≃ₗ[k] n} (p : Product e) (x : g) : Module.End k g :=
  p.mul.flip x
```

The fields `skew`, `left_lie` and `derivation` are the three identities of Burde and Dekimpe's Definition 2.1 (the paper's (1) to (3)), and `right p x` is the right multiplication $y \mapsto y \cdot x$. The main results, in `PostLie/Statement.lean`, are

```lean
theorem solvable_of_trace_right_eq_zero (e : g ≃ₗ[k] n) (p : Product e)
    [LieRing.IsNilpotent n]
    (htrace : ∀ x, LinearMap.trace k g (right p x) = 0) :
    LieAlgebra.IsSolvable g

theorem no_product_of_perfect (e : g ≃ₗ[k] n)
    [LieRing.IsNilpotent n] [Nontrivial g]
    (hperfect : ⁅(⊤ : LieIdeal k g), (⊤ : LieIdeal k g)⁆ = ⊤) :
    ¬ Nonempty (Product e)
```

These are the paper's Theorem 1.1 and Corollary 1.2. `Nontrivial g` says that the algebra is nonzero, and `hperfect` that it equals its derived algebra.

## Axioms

`PostLie/Audit.lean` prints the axioms of both theorems under `#guard_msgs`, so the build fails unless they are exactly `propext`, `Classical.choice`, `Quot.sound` and the two cited theorems in `PostLie/Textbook.lean`:

- `PostLie.levi_nonzero_semisimple`: a finite-dimensional Lie algebra over a field of characteristic zero that is not solvable has a nontrivial subalgebra `s` with `LieAlgebra.IsSemisimple k s`. This follows from Levi's theorem, Weibel, *An Introduction to Homological Algebra* (1994), Theorem 7.8.13, since a non-solvable algebra has a nonzero Levi factor.
- `PostLie.whitehead_first`: for a finite-dimensional semisimple `s` and a finite-dimensional representation `ρ` of `s` on `M`, every linear `c : s →ₗ[k] M` with `c ⁅x, y⁆ = ρ x (c y) - ρ y (c x)` has the form `c x = ρ x m` for one `m : M`. This is Whitehead's first lemma, Weibel, Corollary 7.8.10.

Both docstrings quote Weibel's statements. The paper's Section 6 states both theorems and how they match Mathlib's definitions.

## Layout

- `PostLie/Definitions.lean`: `Product` and `right`.
- `PostLie/Basic.lean`, `PostLie/Action.lean`: the representation $L$ as a map to derivations (`action`), the identity map as a cocycle (`identification_isCocycle`), the identity $`R(x) = L(x) - \mathrm{ad}_{\mathfrak g}(x) + \mathrm{ad}_{\mathfrak n}(x)`$ and the trace facts (`trace_action_eq_trace_ad`, `trace_right_of_perfect`).
- `PostLie/Cocycle.lean`: cocycles (`IsCocycle`) and the trace identity used in Lemma 3.1 (`trace_velocity_of_cocycle`).
- `PostLie/Translation.lean`, `PostLie/ExponentialRemainder.lean`: the derivation $A$ of the semidirect sum, its nilpotency and the conjugate cocycle (`translated`, `translated_isCocycle`).
- `PostLie/Jacobi.lean`, `PostLie/PolynomialFlow.lean`, `PostLie/Determinant.lean`, `PostLie/TranslationPolynomial.lean`: Jacobi's formula over $k[t]$, the truncated exponential as a polynomial matrix, and the paper's Lemma 3.1 (`det_translated`, `translated_bijective`).
- `PostLie/Filtration.lean`, `PostLie/Subquotient.lean`, `PostLie/WhiteheadStep.lean`: the lower central series, its quotients as modules and the paper's Lemma 4.1 (`whitehead_correction`, `translated_mod_next`).
- `PostLie/Solvability.lean`: the induction along the lower central series (`cocycle_into_centralTerm`) and the proof of Theorem 1.1 (`solvable_of_invertible_cocycle`).
- `PostLie/Statement.lean`: the two main results; `PostLie/Audit.lean`: the axiom checks.
- `PublicChecks.lean`: both results restated with their full types, and the zero product on any Lie algebra over itself, an example of the definition to which the theorem applies.

## What is outside Lean

Levi's theorem and Whitehead's first lemma are assumed as the two axioms above. Mathlib at the pinned commit has neither.
