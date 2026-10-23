# Lean proof

With [elan](https://github.com/leanprover/elan) installed, run from this directory:

```sh
lake exe cache get
lake build
```

Elan installs the toolchain in `lean-toolchain`, Lean 4.34.0. Mathlib
v4.34.0 and all transitive dependencies are pinned in `lake-manifest.json`.
To replay the proof without this project's previous build products, run
`lake clean` and then `lake build`.

The build checks the definitions in `Statement.lean`, the proof in
`LitOnlySigma.lean`, the deleted-state control in `Controls.lean`, the
expanded theorem types in `Check.lean`, and the axiom guards in `Audit.lean`.
The graph and starting lights are checked by `graph_is_cycle_complement`
and `start_lights`. The endpoint is
`LitOnlySigma.counterexample : CounterexampleStatement`, whose type expands to:

```lean
Undirected graph ∧ Connected graph ∧
regularMinimum graph start = 0 ∧ litOnlyMinimum graph start = 4 ∧
(∀ m, ¬ CompleteMultipartite graph m) ∧ ¬ Conjecture5 graph
```

`LitOnlySigma.not_conjecture5 : ¬ Conjecture5 graph` is the direct
refutation. The proof also establishes `4 ≤ discrepancy graph` and
`7 < 2 * discrepancy graph`; it does not assert an exact graph-wide gap
or minimality of the example. [FAITHFULNESS.md](FAITHFULNESS.md) compares
the definitions with the source.

The finite certificate checks use kernel reduction (`decide`). Induction
on reflexive transitive reachability then proves the bound for every finite
move sequence, with no depth limit. No search program or external
certificate checker is imported. The Lean literals describe the same graph,
start and closed set as `../data/certificate.json`. The deleted-state
control proves that removing state 45 breaks closure, as the two Python
checkers also detect.

`Audit.lean` checks every declaration in the `LitOnlySigma` namespace and
uses `#guard_msgs in #print axioms` for the endpoints and the main bridge
lemmas. The guards require exactly `propext`, `Classical.choice` and
`Quot.sound`; an additional axiom or proof hole fails the build. To replay
the audit separately:

```sh
lake env lean Audit.lean
```

The trusted base is Lean's kernel and these standard logical foundations,
together with the source correspondence described in the faithfulness note.
