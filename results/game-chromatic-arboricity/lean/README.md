# Lean development

Run `lake exe cache get` and then `lake build` in this directory. `lean-toolchain` selects Lean v4.34.0, and `lakefile.toml` pins Mathlib to commit `5ed2965256430c3649e86755f9576b54eca72435` (with the full dependency set in `lake-manifest.json`). The default build checks the library `GCG` and the files `Main.lean` and `Axioms.lean`. With the Mathlib cache it takes about a minute and under 8 GB of memory.

## Definitions

The game is defined in `GCG/Game.lean`. A position is a map `c : V → Option (Fin k)`, with `none` for an uncolored vertex.

```lean
def Move (G : SimpleGraph V) {k : ℕ} (c c' : V → Option (Fin k)) : Prop :=
  ∃ v i, c v = none ∧ (∀ w, G.Adj v w → c w ≠ some i) ∧ c' v = some i ∧
    ∀ u, u ≠ v → c' u = c u

inductive AliceWins (G : SimpleGraph V) (k : ℕ) : Bool → (V → Option (Fin k)) → Prop
  | full (b : Bool) (c : V → Option (Fin k)) : (∀ v, c v ≠ none) → AliceWins G k b c
  | alice (c c' : V → Option (Fin k)) :
      Move G c c' → AliceWins G k false c' → AliceWins G k true c
  | bob (c : V → Option (Fin k)) :
      (∃ c', Move G c c') → (∀ c', Move G c c' → AliceWins G k true c') →
      AliceWins G k false c

def AliceWinsGame (G : SimpleGraph V) (k : ℕ) : Prop :=
  AliceWins G k true (fun _ => none)
```

`Move G c c'` says that `c'` comes from `c` by giving one uncolored vertex a color that none of its neighbors has. `AliceWins G k b c` says that Alice can force a win from `c`, with Alice to move when `b = true`: every vertex is colored, or Alice has a move to a winning position, or Bob has a move and every move of his leads to a winning position. A player with no legal move ends the game, and Alice has won exactly when every vertex is colored. On a finite graph every play ends, so `¬ AliceWinsGame G k` says that Bob wins the `k`-color game on `G`. The game chromatic number of `G` exceeds `K` when this holds for every `k ≤ K`.

`C4Free G` (in `GCG/Game.lean`) says that there are no `a, b, c, d` with `a ≠ c`, `b ≠ d` and `a ~ b ~ c ~ d ~ a`. `ArboricityLE G d` (in `GCG/Forest.lean`) says that some map from the unordered pairs of vertices to `Fin d` makes every color class of edges of `G` a forest, that is, `G` has arboricity at most `d`. Because the map is defined on all pairs, `ArboricityLE G 0` fails for every graph with a vertex; this only affects `d = 0`.

## Statements

The cited theorem, in `Main.lean`, is the proposition

```lean
def C4FreeSubgraphTheorem : Prop :=
  ∀ t : ℕ, ∃ d : ℕ, ∀ (V : Type) [Finite V] [Nonempty V] (G : SimpleGraph V),
    d * Nat.card V ≤ 2 * G.edgeSet.ncard →
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ C4Free H.coe ∧
      t * H.verts.ncard ≤ 2 * H.coe.edgeSet.ncard
```

It is Theorem 4.2 of the paper: every finite graph with at least one vertex and average degree at least `d` has a subgraph with at least one vertex, no 4-cycle and average degree at least `t`. The paper derives it from Theorem 1 of Kühn and Osthus (Combinatorica 24 (2004)), which gives a subgraph of average degree at least `t` and girth at least six: for `t = 0` a single vertex serves, and for `t ≥ 1` that subgraph has an edge, hence a vertex, and no 4-cycle. Theorem 1.1 of Montgomery, Pokrovskiy and Sudakov (Israel J. Math. 246 (2021)) gives an explicit `d` for `t ≥ 1`. The two main results, in `Main.lean`, are

```lean
theorem GCG.exists_subgraph_bob_wins (hC4 : C4FreeSubgraphTheorem) (K : ℕ) :
    ∃ d : ℕ, ∀ (V : Type) [Finite V] [Nonempty V] (G : SimpleGraph V),
      d * Nat.card V ≤ 2 * G.edgeSet.ncard →
      ∃ H : G.Subgraph, ∀ k ≤ K, ¬ AliceWinsGame H.coe k

theorem GCG.bounded_arboricity (hC4 : C4FreeSubgraphTheorem) (K : ℕ) :
    ∃ d : ℕ, ∀ C : (V : Type) → SimpleGraph V → Prop,
      (∀ V G, C V G → Finite V) →
      (∀ V G, C V G → ∀ H : G.Subgraph, C H.verts H.coe) →
      (∀ V G, C V G → ∃ k ≤ K, AliceWinsGame G k) →
      ∀ V G, C V G → ArboricityLE G d
```

These are the paper's Theorem 1.1 and Corollary 1.2. A Mathlib subgraph `H : G.Subgraph` is a set of vertices with a set of edges among them, and `H.coe` is the graph it forms. In the corollary a class of graphs is a predicate `C`; the three hypotheses say that its members are finite, that it is closed under subgraphs and that each member has game chromatic number at most `K`.

## Axioms

`Axioms.lean` prints the axioms of `GCG.exists_subgraph_bob_wins`, `GCG.bounded_arboricity` and `GCG.bob_wins_of_structure` (the paper's Theorem 2.1) under `#guard_msgs`, so the build fails unless they are exactly `propext`, `Classical.choice` and `Quot.sound`. The cited theorem is not a Lean axiom: both main theorems take it as the hypothesis `hC4`, and their proofs establish its hypotheses for each graph to which they apply it.

## Layout

- `GCG/Game.lean`: `Move`, `AliceWins`, `AliceWinsGame`, `C4Free`.
- `GCG/Potential.lean`: Bob's potential strategy, `bob_wins_of_structure` (Theorem 2.1).
- `GCG/Extract.lean`: `exists_minDegree_subset` (Lemma 3.1, for integer thresholds `t`, the case the main proof uses) and `extract` (Lemma 3.2).
- `GCG/Forest.lean`: `ArboricityLE` and `arboricityLE_of_degenerate`, the degeneracy step of Corollary 1.2.
- `Main.lean`: `pickGraph` and `bob_wins_pickGraph` (Corollary 2.2 under the stronger hypothesis `(2^K + 1)|U| < |A|`, the case the main proof uses; the paper's weaker hypothesis follows from Theorem 2.1 by its written proof), `C4FreeSubgraphTheorem`, `exists_subgraph_bob_wins` (Theorem 1.1) and `bounded_arboricity` (Corollary 1.2).
- `Axioms.lean`: the axiom checks.

## What is outside Lean

Only the theorem of Kühn and Osthus, as the hypothesis above. Mathlib at the pinned commit does not have it.
