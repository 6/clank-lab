# Lean proof

The proofs, the Lean formalization and the text were produced by AI models
(from OpenAI and Anthropic), working under the author's direction.

With [elan](https://github.com/leanprover/elan) installed, run from this directory:

```sh
lake exe cache get
lake build
```

The project pins Lean 4.19.0 and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. The first command retrieves
Mathlib's compiled cache; the second builds the proof and the checks in
[Checks.lean](Checks.lean). No separate script is needed.

## Definitions

[Hopkins/Definitions.lean](Hopkins/Definitions.lean) holds every
definition the statement uses. A coloring is a function `c : ℕ → Bool`,
with `true` for color 1; only its values on $1, \dots, N$ matter.

- `Valid N c`: `c 1 = false`, and no `i` with $1 \le i$ and $i + 1 \le N$
  has `c i = true` and `c (i + 1) = true`. This is a golden-mean coloring
  of $1, \dots, N$ that starts with color 0.
- `Mono a b N c`: there are `x y z`, each between 1 and `N`, with
  `a * x + b * y = z` and `c x = c y`, `c y = c z`. The inputs may be equal.
- `Forces a b N`: every `c` with `Valid N c` has `Mono a b N c`.
- `ForcingSet a b`: the positive `N` with `Forces a b N`.
- `R0phi a b := sInf (ForcingSet a b)`: Hopkins's golden Rado number,
  the least positive `N` with the forcing property.

## Main theorems

```lean
theorem Hopkins.formula_isLeast (a ell : ℕ) (ha : 2 ≤ a) (hell : 1 ≤ ell) :
    IsLeast (ForcingSet a (a * ell)) (a ^ 2 * (ell + 1) ^ 2)

theorem Hopkins.formula (a ell : ℕ) (ha : 2 ≤ a) (hell : 1 ≤ ell) :
    R0phi a (a * ell) = a ^ 2 * (ell + 1) ^ 2
```

`formula_isLeast` is the theorem of the paper: $a^2(\ell+1)^2$ has the
forcing property and no smaller positive integer does. `formula` reads off
the value of `R0phi` from it, so the convention for the infimum of an empty
set plays no part. The two bounds are also separate theorems:

- `Hopkins.upper`: for all $a, \ell \ge 1$,
  `Forces a (a * ell) (a ^ 2 * (ell + 1) ^ 2)` (the upper bound needs no
  hypothesis on $a$);
- `Hopkins.lower`: for $a \ge 2$, $\ell \ge 1$ and $1 \le M < a^2(\ell+1)^2$,
  the coloring `lowerColor a ell` is valid on $1, \dots, M$ and has no
  monochromatic solution there. It gives color 1 exactly to the multiples
  of $a$ that are at least $a(\ell+1)$.

The files follow the paper: [Core.lean](Hopkins/Core.lean) has the
forcing lemmas, the residue bounds and the descent (`initial_residue`),
[Upper.lean](Hopkins/Upper.lean) the shift argument and the contradiction, [Lower.lean](Hopkins/Lower.lean) the
coloring, and [Formula.lean](Hopkins/Formula.lean) the two theorems above.

## Checks

[Checks.lean](Checks.lean) restates each definition and the four theorems
with their exact types, so the build fails if any of them changes. It
checks the instances `R0phi 2 2 = 16` (Hopkins's Theorem 2 at $a = 2$) and
`R0phi 2 4 = 36`. [SourceControls.lean](Hopkins/SourceControls.lean)
proves Hopkins's values `R0phi 1 1 = 4` and `R0phi 1 2 = 4` (Hopkins's Theorem 1)
directly from the definitions; the second is where the printed formula
fails at $a = 1$, $\ell = 2$.

The axiom report of every main theorem is fixed with `#guard_msgs`: each
depends only on `propext`, `Classical.choice` and `Quot.sound`. There is no
`sorry`, no added axiom and no `native_decide`.
