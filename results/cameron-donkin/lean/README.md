# Lean proof of arbitrary finite avoidance of 3

`Donkin.arbitraryDelay` proves `Donkin.ArbitraryDelay`: for each positive
integer $n$, there is a prime seed whose first $n$ terms avoid 3. The seed
counts as the first term. `Endpoint.lean` defines the sequence by taking the
least prime factor of one plus the product of all preceding terms.

The proofs, the Lean formalization and the text were produced by AI models
(from OpenAI and Anthropic), working under the author's direction.

With [elan](https://github.com/leanprover/elan) installed, run these commands
from this directory:

```sh
lake exe cache get
lake build
```

`lean-toolchain` pins Lean, and the Lake configuration and manifest pin
Mathlib and its dependencies. Mathlib supplies the Chinese remainder theorem,
Dirichlet's theorem on primes in arithmetic progressions, and the finite-field
and least-prime-factor facts used in the proof.

## Formal statement

The definitions use zero-based indices: `term p 0 = p`. The exact endpoint is

```lean
∀ n : ℕ, 0 < n → ∃ p : ℕ, Nat.Prime p ∧
  ∀ j : ℕ, j < n → Donkin.term p j ≠ 3
```

`Checks.lean` also derives the vacuous zero-length case and proves that
`productState p k` is the product of terms indexed from 0 through $k$.
Consequently the recursion is precisely the product-plus-one recurrence.
The seed may depend on $n$; the assertion that one prime seed avoids 3
forever remains a separate question.

## Proof structure

`HardStep.lean` proves simultaneous compatibility of the required residues
at each prime. `Dependencies.lean` obtains auxiliary primes and prime seeds
from Dirichlet's theorem and the Chinese remainder theorem. `Assembly.lean`
combines those congruences to prescribe the least prime factors of a finite
initial segment. `FullProof.lean` constructs an increasing tail of auxiliary
primes and proves `Donkin.arbitraryDelay`.

The endpoint's docstring says that no proof is asserted in that file.
`Endpoint.lean` contains only the definitions and statement;
`FullProof.lean` supplies the proof. The original docstring is retained with
the checked source.

## Build checks

The default `lake build` imports `Checks.lean`, so it checks the exact
endpoint type, the recurrence, and the sample sequences beginning at 2, 5
and 7. Those sequences begin `[2, 3, 7]`, `[5, 2, 11, 3]` and
`[7, 2, 3, 43, 13, 53]`, respectively.

The axiom guards require that the main theorem and the principal lemmas
depend on exactly `propext`, `Classical.choice` and `Quot.sound`. A changed
axiom report fails the build. No compiled evaluation is used to prove the
statement: these proofs do not depend on `Lean.ofReduceBool` or
`Lean.trustCompiler`.

Dependencies and their licenses are described in
[THIRD_PARTY.md](../THIRD_PARTY.md).
