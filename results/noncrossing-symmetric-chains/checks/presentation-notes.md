# Checking notes

The paper combines exact group computations and written arguments with Lean
checks of the general lemmas. The following details describe the unchanged
verification package.

## Published verification description

These details retain the first edition’s mathematical and computational
dependencies.

The companion verification package
(`noncrossing-symmetric-chains-v2`) accompanies this paper.
Its folder contains the compressed interval and chain
certificates in `data/`, the exact models and checkers in
`checks/`, and the Lean development in `lean/`. The
README gives the executable entry point and the ordinary Lake build.
The finite verification uses Python, JavaScript, and GAP, including
GAP's SmallGrp library, which its conjugacy-class algorithms require.
No chain-search code is loaded by the verification.

The chains were found using Griggs's matching construction (Griggs, 1977) in the
iterative form described by Tomon (Tomon, Sections 3–4). It starts
with singleton chains in the middle rank when the total rank is
even, or a perfect matching between the two middle ranks when it
is odd. At each
stage, a bipartite perfect matching either extends a chain at both
ends by one cover or leaves it finished. Two copies of each active
chain, joined by an identity edge, allow these choices in a single
matching problem. The implementation uses NumPy and SciPy on CPUs.
Verification requires only the resulting explicit chains, with no
dependency on this matching implementation.

The interval generator and semantic checker have separate graph
traversals and rank implementations. They share the exact models and
GAP's exact field and permutation-group arithmetic. An independent
chain checker does not replace the interval-completeness proof: that
proof is the paper’s finite interval criterion, instantiated by the
semantic checks. Removing a genuine interior vertex or a genuine edge
is rejected by the full semantic check. Each chain checker also
rejects omitted or repeated chains, asymmetric endpoints, and corrupted
chain order. These controls test failures of the
certificates rather than supplying additional mathematical premises.

The Lean endpoint in `Endpoint.lean` specifies exactly a
partition of the absolute-order interval into nonempty saturated
chains, with ranks given by reflection length and endpoint sum equal
to the essential rank. Its eligibility and Coxeter predicates are
explicit semantic parameters. `GeneralEndpoint` is this
specification; it is not an unconditional theorem of Lean about
complex reflection representations.

The proved Lean components are the interval-closure criterion and rank
conclusion of the paper’s finite interval criterion, the explicit grid product
construction and its cover relation, reflection-word length and
interval transport under reflection-preserving isomorphisms, the
displayed split of the exceptional-type table, and finite products
including the empty product. The Lake build checks these proofs.
The finite GAP outputs are not imported into Lean.

The external mathematical inputs are the published classification and
well-generated filter; the earlier family and small-exceptional
decompositions; the identification of the exact models and invariant
degrees; and the reflection-automorphism theorem. The elementary
matrix-rank and reflection-word arguments connecting the finite model
to absolute order are given in full in the paper. The computational trusted
base includes exact arithmetic, group membership, eigenvectors, and
complete conjugacy-class algorithms in GAP, together with the
interpreters, parser and checker implementations, and Lean's
compiler and kernel. In particular the class-size check supplements
GAP's class enumeration; it does not independently reprove that
enumeration algorithm.

No symmetric Boolean decomposition is asserted for the new exceptional cases.

This yields the stated computer-assisted theorem, with Lean checks of
its general combinatorial lemmas. It yields neither a uniform formula
for the new chains nor symmetric Boolean decompositions for the six
exceptional intervals.


## Formal dependencies

The guarded reports in `lean/Check.lean` record `propext`, `Classical.choice`
and `Quot.sound` for the product and reduction constructions; some transport
lemmas need fewer. `IntervalCertificate.exact_interval` and
`IntervalCertificate.certified_rank` use `propext` and `Quot.sound`.
The development uses only Lean's standard library and no added axioms,
`sorry` or `native_decide`. The finite GAP outputs are external to Lean.

## Presentation reproduction

The PDF is built with pdfLaTeX twice, with `SOURCE_DATE_EPOCH=1792886400`
and `FORCE_SOURCE_DATE=1`, in a temporary directory; only `paper.tex` and
`paper.pdf` belong in the paper directory. Independent builds must agree
byte for byte. Rebuilding this PDF does not execute the mathematical checks.
