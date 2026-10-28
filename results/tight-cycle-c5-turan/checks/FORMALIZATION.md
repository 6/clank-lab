# Formal statement and checking

The paper's main formal theorem is
`TightCycleC5.Bridge.mubayi_rodl_checked`. Its type is

```lean
Filter.Tendsto
  (fun n : ℕ => (TightCycleC5.ex n : ℝ) / (n.choose 3 : ℝ))
  Filter.atTop (nhds (2 * Real.sqrt 3 - 3))
```

`TightCycleC5.ex n` is the maximum over all labeled three-uniform
hypergraphs on `Fin n` avoiding an injective cyclic five-vertex edge map.
Additional edges on the five vertices are allowed. The empty graph is
included. There are no graph, partition or certificate assumptions in the
closed theorem. Division is the total real-field operation; the zero
denominators for `n < 3` affect only finitely many initial terms.

The two closed inputs are
`TightCycleC5.Bridge.P32ClassBridge.p32` and
`TightCycleC5.Bridge.p33_checked`. They prove the paper's two partition
propositions: the first chooses ε before N; the second chooses ξ before
δ and N, which precede n, H and S. Bad-minus-missing is real subtraction.
The reduction is `TightCycleC5.mubayi_rodl_of_bllp`. Empty and full cuts
are included in the cut definitions.

## Toolchain and trust boundary

The development uses Lean 4.32.2 and Mathlib revision
`905b95818eb32af7874a58b427f50c1711a5e96c`.

In addition to `propext`, `Classical.choice` and `Quot.sound`, the endpoint
depends on exactly 692 named compiler-trusted `native_decide` facts:

- 53 groups of uncolored arithmetic checks;
- one multiplier quotation identity;
- 634 colored arithmetic checks;
- two sparse coefficient comparisons;
- two rational Gram identities.

The uncolored and colored propositions depend on 54 and 638 of these
facts, respectively. They trust Lean's compiler and runtime as well as
the kernel. The class covers, arithmetic-range coverage, all six
uncolored positive-semidefinite matrices and the other 36 colored
matrices have kernel proofs. The rational class inequalities cover 835
uncolored and 40,547 colored classes. The guard checks the exact allowed
names, rather than just these totals.

## Recorded execution and reproduction

The independent accepted full replay checked 1,433 mathematical modules;
it used about 48.10 CPU-hours, with maximum per-module peak memory about
11.02 GiB. The subsequent main-only inventory verification is a hash and
transfer audit, not a second full replay. The accepted frozen mathematical
source closure has SHA-256
`9a7475cd2d065367fc2cf2b2fbfeaab7cdf704386946b63d5e7af88129e12f55`.
The source-preservation audit compared all 1,433 accepted source hashes:
1,428 public exports are byte-identical and five differ only in comments;
all uncommented proof bytes are preserved. This historical fingerprint is
not a claim that the public archive is byte-identical to the private
acceptance packet. The public materialization manifest independently
binds the shipped source bytes.

A later, separate check compiled the actual `PublicGuard` adapter and
ran a fresh `FinalAcceptance` exact-type probe against the accepted frozen
objects and dependencies. The probe exercises the theorem above, both
partition expansions and the exact-name guard for the 692 compiler-trusted
facts and three standard axioms. It does not repeat the full dependency
proof replay. **A plain standalone `lake build` and its scheduling were
not exercised by that adapter check.** The configured Lake target and
the reproduction commands in [the Lean guide](../lean/README.md) describe
how to reproduce the check; their presence is not an execution receipt.

The Python commands and materialization procedure are in
[the checking guide](README.md). Separately, two independent exact
implementations for each certificate reconstruct its coefficients and
cover, check rational positive semidefiniteness, accept the certificate
and reject altered coefficients, invalid matrices and incomplete class
covers. The proof uses the exact identities, not numerical solver output.
Bodnár, León, Liu and Pikhurko's notebook, code cell 6, supplies a
comparison certificate for forbidding both the tight four-cycle and the
tight five-cycle. The present certificates concern the five-cycle alone:
[pinned notebook](https://github.com/bodnalev/supplementary_files/blob/5766324d010da24a66271c0fbe38460cd377985b/no_cl/no_c5_k4.ipynb).
