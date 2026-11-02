# Lean proof

The project uses Lean 4.19.0 (`lean-toolchain`) and Mathlib at commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. `lakefile.toml` and
`lake-manifest.json` pin Mathlib and every transitive package to immutable
commits. Dependencies are downloaded, not included in this distribution.

With elan installed, use the standard commands:

```sh
lake exe cache get
lake build
```

The main theorem is `BaseREhrhart.allTEhrhart : BaseREhrhart.AllTEhrhartClaim`.
`BaseREhrhart/Statement.lean` defines every part of this proposition before
any proof: `simplex` is Mathlib's `convexHull ℝ` of the five unit vectors of
`Fin 5 → ℝ` and the point $-c$ with $c = (13, 182, 2548, 35672, 499408)$;
`dilate t` is the image of `simplex` under $y \mapsto t \cdot y$, for every
natural number $t$ including zero; `LatticePoints t` is the type of integer
vectors whose real coordinates lie in `dilate t`; and `AllTEhrhartClaim`
states that `Nat.card (LatticePoints t)`, cast to the rationals, equals the
polynomial of the paper's Theorem 1 for every natural $t$. There are no
other hypotheses.

`BaseREhrhart/Main.lean` also proves
`actual_lattice_count_and_negative_coefficient` (the count is the
evaluation of a polynomial in `Polynomial ℚ` whose coefficient of $X$ is
$-268/15 < 0$), `latticePointsFinite` (each `LatticePoints t` is finite,
so `Nat.card` is an ordinary count), `lattice_count_zero`, and, in
`Independence.lean`, `vertices_affineIndependent` (the six vertices are
affinely independent).

The modules follow the paper's proof. `Geometry` and `Decomposition` prove
Lemma 2 (`mem_dilate_iff_integerCone`) and the bijection of Lemma 3
(`latticeEquivPieces`). `StarsBars` and `Counting` give Corollary 4.
`Polynomial` expands the binomial coefficients, including the small values
of $t$. `CertificateCore`, the four `CertificateChunk` files and
`Certificate` prove Proposition 5 (`height_histogram`): 38 block sums of
$2^{20}$ raised to the height, each checked with ordinary `decide` by kernel
reduction, a proof that the blocks cover all 537,824 residues, and
uniqueness of digits in base $2^{20}$. No `native_decide` is used.

`BaseREhrhart/Checks.lean` is imported by the default build. It
type-checks the main theorem against the displayed polynomial, checks that
the fifth vertex is $-13 \cdot 14^{i}$ coordinatewise, that the residue
count is $14^5$, that the heights sum to it, and that the simplex itself
contains 8,573 lattice points. Guarded axiom reports for the main theorems
require exactly `propext`, `Classical.choice` and `Quot.sound`.

Peak memory during the build is about 6 GB, in the certificate modules.
In supplementary runs that are not distributed here, two altered
certificates, one with a block value increased by one and one with the
last block of residues omitted, were rejected by the kernel.
These checks are distinct from expert review.
