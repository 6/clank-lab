# Lean proof of the Elgin–Reading–Stella conjecture on $\tau^{1,5}(2j,j)$

The theorem `ErsConj13.ers_conjecture_13` in `Main.lean` states that the
scattering diagram $D(1+x,\,1+y^5)$ has a consistent family of wall functions,
and that for every consistent family the coefficient of $t^j$ in the function on
the ray $(2,5)$, with $t = x^2y^5$, equals

$$\frac{1}{j}\sum_{\ell} \binom{\ell}{j+1-\ell}\binom{j+\ell-1}{\ell} \qquad (j \ge 1).$$

That coefficient is $\tau^{1,5}(2j,j)$ as defined by Burcroff, Lee, Mou,
Musiker and Reineke (arXiv 2511.14672, eq. (2.2)), the convention of the
table and code of Elgin, Reading and Stella. The paper's remark on
conventions explains the identification.

The proofs, the Lean formalization and the text were produced by AI models
(from OpenAI and Anthropic), working under the author's direction.

With [elan](https://github.com/leanprover/elan) installed, run these commands
from this directory:

```sh
lake exe cache get
lake build
```

Elan installs the Lean version selected by `lean-toolchain`, and the manifest
pins Mathlib. The build needs about 8 GB of memory and, with the Mathlib
cache, a few minutes. It checks every proof, the examples and the axiom
guards.

## What to read

- `ErsConj13/ScatDefs.lean` defines the scattering diagram. A wall
  $\theta_{r,f}$ is the substitution $x \mapsto x f(z^r)^{r_2}$,
  $y \mapsto y f(z^r)^{-r_1}$ on $\mathbb{Q}[[x,y]]$, and
  `IsConsistentFamily P₁ P₂ f` says that every $f_r$ has constant term 1 and
  that, for every $N$, the product of the walls with $r_1 + r_2 < N$ in
  ascending order of slope agrees with
  $\theta_{(0,1),P_2} \circ \theta_{(1,0),P_1}$ on $x$ and $y$ modulo
  $(x,y)^N$. Its docstring explains how this matches the consistency
  condition of Gross, Pandharipande and Siebert.
- `ErsConj13/Defs.lean` defines `ersCoeff j`, the conjectured value, and the
  series `S`.
- `Main.lean` states and proves `ers_conjecture_13`. It needs no other file
  to be read beyond these two definition files.
- `Realization.lean` proves `ray21_eq_S5`: the ray-$(2,1)$ function of
  $D((1+x)^5,\,1+y)$ is $S^5$.
- `MainLemma.lean` proves `main_lemma`: the diagonal wall function of the
  fifth power of the explicit automorphism $T$ is $S^5$, given the
  filtration properties of the two halves of its ordered factorization.
- `ErsConj13/` holds the rest of the proof: ordered factorization
  (existence and uniqueness, `KS.lean`, `KSExist.lean`), the change of
  lattice (`R2Pieces.lean`), the transport to $D((1+x)^5, 1+y)$ and the
  realization (`R1Pieces.lean` and the files it imports), the filtration,
  cocycle and ODE argument (`Pieces.lean`) and the binomial sum
  (`Binomial.lean`, `Telescoping.lean`).
- `Examples.lean` checks small cases of the definitions: the first values of
  `ersCoeff`, the bracket on monomials, and the ray of each slope.
- `Axioms.lean` uses `#guard_msgs` to require that the main theorems depend
  on exactly `propext`, `Classical.choice` and `Quot.sound`; a changed axiom
  report fails the build.

No theorem is assumed: ordered factorization, the change of lattice and the
uniqueness of the differential equation's solution are all proved here.

Dependencies and their licenses are described in
[THIRD_PARTY.md](../THIRD_PARTY.md).
