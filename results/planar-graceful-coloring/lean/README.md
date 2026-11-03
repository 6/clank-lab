# Lean development

Run `lake exe cache get` and `lake build` in this directory. The default build checks the library `Antony24` and the file `PublicChecks.lean`, which restates both main theorems with their full types, guards their axioms and checks two examples. The guarded axiom prints permit exactly `propext`, `Classical.choice` and `Quot.sound`. The proof does not use compiled evaluation; the finite case tables are checked by the kernel with `decide`.

## Dependencies

- Lean **v4.19.0**, selected by `lean-toolchain`.
- Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, selected by `lakefile.toml`.
- Transitive dependencies are pinned by revision in `lake-manifest.json`.

Mathlib and the Lean toolchain are obtained as dependencies; their source is not redistributed here.

## Statements and correspondence

The main theorem is `Antony24.graceful4_s2_iff_pmc` in `Antony24/Main.lean`:

```lean
theorem graceful4_s2_iff_pmc {V : Type*} [Finite V]
    (G : SimpleGraph V) (hG : Cubic G) :
    Graceful4 (S2 G) ↔ PMC G
```

`Antony24.four_labels_s2_iff_perfectMatching_equal_cut` states the same equivalence with every definition unfolded to the usual one: labels from 1 to 4 on the left, and a Mathlib perfect matching whose edges are exactly the edges of the graph that cross a vertex set $A$ on the right.

The definitions are in `Antony24/Basic.lean`.

- `SimpleGraph V` is Mathlib's finite-or-infinite simple graph; only `[Finite V]` is assumed. There is no connectedness, nonemptiness or planarity hypothesis, so the theorem covers the empty graph and disconnected graphs.
- `Cubic G` says that every vertex has exactly three distinct neighbors; `cubic_iff_degree_three` and `cubic_iff_regular_three` relate it to Mathlib's degree.
- `IsGraceful G c` for `c : V → Fin 4` says that adjacent vertices get distinct colors and that two distinct neighbors `u`, `w` of a vertex `v` give distinct differences `|c v - c u|` and `|c v - c w|`. `Graceful4 G` says such a `c` exists. Neither injectivity nor surjectivity of `c` is required. `graceful4_iff_four_labels` proves the equivalence with natural-number labels from 1 to 4.
- `S2 G` is the double subdivision. Its vertex type is `V ⊕ Dart G`, where a dart is an ordered pair `(u, v)` of adjacent vertices. The edge `uv` becomes the path `u — (u,v) — (v,u) — v`.
- `PMC G` says that some `side : V → Bool` gives every vertex exactly one neighbor on the other side. `pmc_iff_perfectMatching_equal_cut` proves that this is the existence of a perfect matching equal to the whole cut of a vertex set.

`Antony24/Union.lean` proves that both properties behave as conjunctions under disjoint unions (`graceful4_union_iff`, `pmc_union_iff`), that a disjoint union of cubic graphs is cubic (`cubic_union`) and that double subdivision commutes with disjoint union up to isomorphism (`unionS2Iso`, `graceful4_s2_union_iff`). None of these needs finiteness, and the paper's reduction does not use them. `Antony24/Properties.lean` proves the vertex and edge counts $|V| + 2|E|$ and $3|E|$ of `S2 G` (`s2_vertex_card`, `s2_edge_card`), its degrees (`s2_degree_internal`, `s2_degree_original`, `s2_degree_le_three`), that it is triangle-free (`s2_triangle_free`) and that it preserves proper colorings, in particular bipartiteness. These give the counts and degrees of the paper's Lemma 5(b) and the triangle-freeness used in its Remark 7.

## What is outside Lean

The hardness of perfect matching cut on cubic planar graphs, from Bonnet, Chakraborty and Duron's Theorem 1 and its proof, is cited and not formalized. Planarity of a double subdivision, the running time of the construction, membership in NP and complexity classes themselves are proved in the paper, not in Lean.

## Layout

- `Antony24/Local.lean`: the possible colors at a vertex of degree three and along a subdivided edge, by `decide` over the four colors.
- `Antony24/Forward.lean`, `Antony24/Counting.lean`: a graceful 4-coloring gives a perfect matching cut.
- `Antony24/Orientation.lean`, `Antony24/Reverse.lean`: a perfect matching cut gives a graceful 4-coloring.
- `PublicChecks.lean`: the statement and axiom checks, and the examples. The complete graph $K_4$ is cubic with no perfect matching cut, so its double subdivision has no graceful 4-coloring; the triangular prism has one, so its double subdivision has one.
