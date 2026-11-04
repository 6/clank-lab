# Lean proof of the counterexamples

From this folder, with [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
```

`lean-toolchain` pins Lean 4.34.0, and `lake-manifest.json` pins Mathlib at tag `v4.34.0` (commit `5ed2965256430c3649e86755f9576b54eca72435`) with its dependencies. The default targets build the proof and `Check.lean`, which restates the main theorems with their exact types and fails unless each depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. No proof uses `sorry`, `native_decide` or a new axiom.

## Definitions (`Statement.lean`)

- `Digraph n`: a Boolean adjacency relation on `Fin n` with no loops. Arcs in both directions between two vertices are allowed, and at most one arc in each direction, as in Kühn, Osthus and Treglown.
- `G.dplus i`, `G.dminus i`: the `i`-th smallest out-degree and in-degree (`i = 1, …, n`), from the sorted list of all `n` degrees. The hypotheses only read indices from `1` to `n - 1`.
- `NWHyp G`: for every `i` with `1 ≤ i` and `2 * i < n`, conditions (i) and (ii) of the paper.
- `KOTHyp G`: `NWHyp G`, and condition (iii) when `n` is even.
- `StronglyConnected G`: every vertex reaches every vertex along arcs.
- `HasHamCycle G`: a bijection `c` of `Fin n` with an arc from `c k` to `c (k + 1 mod n)` for every `k`.
- `CycleThrough G a b`: an injective `c : Fin m → Fin n` with an arc from `c k` to `c (k + 1 mod m)` for every `k`, whose image contains `a` and `b`.
- `NashWilliamsConjecture` and `KOTConjecture6`: the two conjectures, for all `n ≥ 3`.
- `G6`, `G7`: the digraphs of `data/G6.txt` and `data/G7.txt`.
- `F u`: the family on `u + 4` vertices, with `U = {0, …, u - 1}`, `w = 0`, `s = u`, `t = u + 1`, `r₁ = u + 2`, `r₂ = u + 3`.

## Theorems (`Main.lean`)

- `kot_counterexample_all (n) (hn : 7 ≤ n) : ∃ G : Digraph n, KOTHyp G ∧ ¬ HasHamCycle G`, and `not_kotConjecture6 : ¬ KOTConjecture6`.
- `counterexample_all (n) (hn : 6 ≤ n) : ∃ G : Digraph n, StronglyConnected G ∧ NWHyp G ∧ ¬ HasHamCycle G`, and `not_nashWilliamsConjecture : ¬ NashWilliamsConjecture`.
- `G6_counterexample`, `G7_counterexample`, and `F_counterexample u (hu : 4 ≤ u)`: strongly connected, `NWHyp`, no Hamilton cycle.
- `G6_no_cycle_through_2_3`, `F_no_cycle_through_s_r1 u` and `F_no_cycle_through_s_r2 u`: no cycle through those pairs of vertices (the last two for every `u`).

## Files

- `Lemmas.lean`: the counting form of the sorted-degree conditions.
- `Small.lean`: `G6` and `G7`, by decision procedures evaluated in the kernel.
- `Family.lean`: the degrees of `F u` for all `u ≥ 4`, strong connectivity, and the argument that the only arc leaving `{t, r₁, r₂}` ends at `w`.
- `Cycles.lean`: the statements about cycles through pairs.
- `Main.lean`: the theorems above.
- `Check.lean`: statement and axiom checks.

The exhaustive search for six or fewer vertices is not in Lean; it is in `checks/`.
