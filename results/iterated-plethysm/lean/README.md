# Lean proof

This is a standalone Lake project. It requires Lean v4.34.0, selected by `lean-toolchain`, and Mathlib v4.34.0 at commit `5ed2965256430c3649e86755f9576b54eca72435`. The checked-in `lake-manifest.json` pins every transitive package to a Git commit. Dependencies are fetched, not included in the bundle. The official Linux x86-64 archive [`lean-4.34.0-linux.tar.zst`](https://github.com/leanprover/lean4/releases/download/v4.34.0/lean-4.34.0-linux.tar.zst) has SHA-256 `caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b` (the release asset digest).

```sh
lake exe cache get
lake build
```

`GR22/Defs.lean` defines the rational symmetric-function ring as a polynomial ring in power sums, with variable index plus one as its weight. Complete homogeneous functions use Newton's recurrence; Schur functions use Jacobi–Trudi; plethysm substitutes Adams operations. `hookCoeff` implements Warning 2.2 of Gutiérrez and Rosas, including the distinguished first part when it equals two and zero for invalid shapes.

`GR22.fullEndpoint : GR22.FullEndpoint` is the paper's general reflection theorem, including vanishing and the column coefficient. Its hypotheses are exactly homogeneity, positive outer degree, inner index at least two, and a Schur expansion. `GR22.expansionsExist` and `GR22.schurExpansion_unique` prove that expansion exists and is unique; these are not assumptions of the result.

`GR22.question1 : GR22.Question1` proves the source's nonzero palindrome statement for every nonempty positive list. `GR22.iterated_has_expansion` supplies its expansion. `GR22.question1Positional : GR22.Question1Positional` proves the reflection with zeros retained, using the product of the nonunit entries other than the last as the outer degree. The empty list is also covered by this latter statement, with plethystic identity and empty product one.

The default build imports `GR22/Checks.lean`. It checks theorem types, both identities $`h_2[h_2]=s_4+s_{22}`$ and $`h_3[h_2]=s_6+s_{42}+s_{222}`$, and the kernel proof that shifting the reflection center by one gives a false statement. Each of the seven exported results has a `#guard_msgs in #print axioms` assertion requiring exactly `propext`, `Classical.choice`, and `Quot.sound`. No compiled-evaluation axiom is used.

The mathematical argument is entirely checked from these definitions. The identification of this standard power-sum presentation with symmetric functions, the correspondence to the source's notation, and the literature discussion are explained in the paper. The PDF itself is not an input to Lean.
