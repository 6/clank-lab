# Lean proof

The project uses Lean 4.34.0 and Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`. Install Lean through
[elan](https://github.com/leanprover/elan), then run in this directory:

```sh
lake exe cache get
lake build
```

The default build includes `Final`, `Statement`, `Examples`, and `Axioms`.
`BLSRestricted` defines the original ordered-tuple polynomial, including
repeated edges and inclusive prefix unions, and proves its deletion
recurrence. `Unit3` expresses it as a finite average of complete homogeneous
polynomials. `H` defines those polynomials recursively and states their
convexity proposition; `Kernel` proves it by a polynomial Hessian
calculation. `Final` combines the two arguments without a residual
convexity assumption.

`Statement` checks both theorem types, the original polynomial formula,
the edge set, and the simplex definition. `Examples` checks degree zero,
the two-variable quadratic complete homogeneous polynomial, repeated edges
with inclusive denominators, and the empty simplex when the edge size
exceeds the number of vertices. `Axioms` makes the build fail if either
endpoint or the complete homogeneous convexity theorem has dependencies
beyond `propext`, `Classical.choice`, and `Quot.sound`. No compiled
evaluation axiom is used by the proof.

The mathematical proof and the Lean source were developed with contributions
from both OpenAI and Anthropic models. The separate acceptance is therefore
same-family, despite being performed in a fresh session. It checked the
literal statement and rejected altered prefix and missing-proof controls.
It is distinct from expert review of the paper. The kernel checks a formal
statement; the comparison of that statement with the cited conjecture is
also described in the paper.
