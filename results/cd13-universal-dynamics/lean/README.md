# Lean proof

The project uses Lean **4.34.0**, source commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and Mathlib **4.34.0**, commit
`5ed2965256430c3649e86755f9576b54eca72435`.
The release tags resolve to those commits in the upstream repositories.
`lean-toolchain` pins Lean; `lakefile.toml` and `lake-manifest.json` pin
Mathlib and every transitive package to immutable commits. Dependencies
are downloaded, not included in this distribution.

With elan installed, use the standard commands:

```sh
lake exe cache get
lake build
```

The main theorem is `CD13.Faithful.full_endpoint : CD13.FullEndpoint`.
`CD13/Endpoint.lean` defines every quantifier of this proposition: a finite
vertex type (possibly empty), an acyclic edge relation, finite nonempty
coordinate sets, a local function reading exactly the outgoing-neighbor
coordinates, an injective monoid homomorphism with the required generator
images, and equality of the universal evaluation kernel with the presented
monoid equality. Ordinary function composition executes a written word
rightmost first. Empty coordinate sets add no constraint to the universal
kernel because their state space is empty.

`CD13/Checks.lean` is imported by the default build. It type-checks the
complete endpoint and elementary empty-graph, one-site and empty-word
examples. Guarded axiom reports for the endpoint and its two principal
recovery results require exactly `propext`, `Classical.choice` and
`Quot.sound`. There is no compiled-evaluation axiom, `sorry`, added axiom,
or exhaustive-search certificate in this proof.

The proof proceeds through finite constructor terms (`Model`), elementary
cancellation (`Reduction`, `HK`, `Presentation`), increasing event sizes
and surviving subterms (`Core`), ordered event histories (`EventHistory`),
dependent pair projections (`PairRecovery`, `Recovery`), trace
reconstruction (`Trace`, `AlgebraBridge`), and the induced action and
faithfulness (`ModelAction`, `Faithful`). `LocalRelations` supplies the
presentation compatibility lemmas.

The full formal claim passed a separate clean-build check, statement
comparison and transitive axiom inspection. A deliberately corrupted
theorem was rejected. These checks are distinct from expert review.
