# Lean proof

From this directory, with elan and Git installed:

```sh
lake exe cache get
lake build
```

The project pins Lean 4.34.0 in `lean-toolchain` and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` in `lakefile.toml`.
`lake-manifest.json` pins transitive dependencies. Nothing outside this
folder is needed. With dependency caches present, allow several minutes.

The files follow the paper's proof:

| Paper | Formal declaration (namespace `SpinningSwitches`) |
| --- | --- |
| Action on configurations | `spin` in `SpinningSwitches/Defs.lean` |
| Prefix coverage, including the empty prefix | `IsSurjectiveStrategy` in `SpinningSwitches/Defs.lean` |
| Excluded-set recurrence and backward tracing | `excl`, `chain`, `not_strategy_of_not_mem` in `SpinningSwitches/Necessity.lean` |
| Coset invariant | `step_aligned`, `excl_aligned` in `SpinningSwitches/Necessity.lean` |
| Prime-order obstruction | `isPGroup_of_strategy` in `SpinningSwitches/Necessity.lean` |
| Central extension construction | `extend_props`, `exists_exclH_univ` in `SpinningSwitches/Sufficiency.lean` |
| Main theorem and two examples | `classification`, `S3_wr_C2_unsolvable`, `A4_wr_C3_unsolvable` in `SpinningSwitches/Main.lean` |

`StatementChecks.lean` checks the complete theorem type, the definition's
quantifier order, and small positive and negative examples. `Axioms.lean`
uses `#guard_msgs in #print axioms` for the classification and the two
negative examples. Their only axioms are `propext`, `Classical.choice`,
and `Quot.sound`; there is no compiled evaluation or additional axiom.
All three roots are built by `lake build`. The proofs establish existence
of a finite strategy and do not claim a minimum length.

Kagey's Theorem 26 correction is prior work: ndkrempel reported on
[MathOverflow](https://mathoverflow.net/a/423643) on December 7, 2025 that
Theorem 26 fails, and Kagey acknowledged the error there on December 8,
2025, noting that Example 27 fails. The formal negative example is a
consequence of the classification, not a claim of priority for the correction.
