# Graceful 4-coloring of planar graphs is NP-complete

[![Checks](https://github.com/6/clank-lab/actions/workflows/planar-graceful-coloring.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/planar-graceful-coloring.yml)

A [graph coloring](https://en.wikipedia.org/wiki/Graph_coloring) assigns colors to the vertices so that adjacent vertices differ. A graceful 4-coloring uses the colors 1, 2, 3, 4 and asks more: at every vertex, the edges leaving it must have distinct differences of their endpoint colors. Cyriac Antony, Laavanya D. and Devi Yamini S. showed in [2024](https://arxiv.org/abs/2407.02179v2) that deciding whether a graph has such a coloring is NP-complete, and that with five or more colors it stays hard on planar graphs; they left open the complexity of the four-color problem on [planar graphs](https://mathworld.wolfram.com/PlanarGraph.html). We prove that it is NP-complete, even for planar graphs in which every vertex has at most three neighbors. Disconnected graphs are allowed, as in their question. The hardness comes from Édouard Bonnet, Dibyayan Chakraborty and Julien Duron's [reduction](https://doi.org/10.1016/j.tcs.2024.114701) showing that it is NP-hard to decide whether a cubic planar graph has a [perfect matching](https://mathworld.wolfram.com/PerfectMatching.html) that is also an edge cut; we apply their construction to every instance. The new step is an exact correspondence: subdividing every edge of a cubic graph twice gives a graph with a graceful 4-coloring exactly when the cubic graph has such a perfect matching.

Written proof, with Lean and computer checks; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Install Lean using [elan](https://github.com/leanprover/elan). A network connection is needed to download the dependencies and their compiled cache. Allow about ten minutes for the download and under a minute for the build, with about 6 GB of memory.

```sh
cd lean
lake exe cache get
lake build
```

The build checks the correspondence for every finite cubic graph, its behavior under disjoint unions, the axioms used and two small examples. [Lean details](lean/README.md) give the dependency pins and how the formal statements match the paper. The cited hardness theorem is not formalized, and the planarity and running-time arguments are in the paper, not in Lean.

## Credits

Cyriac Antony, Laavanya D. and Devi Yamini S. posed the question in *Graceful coloring is computationally hard*, whose published version, by Cyriac Antony, Jacob Antony, Laavanya D. and Devi Yamini S., appeared at CALDAM 2025. Their paper settles five or more colors on planar graphs and four colors on graphs of maximum degree three. The result rests above all on Édouard Bonnet, Dibyayan Chakraborty and Julien Duron's *Cutting Barnette graphs perfectly is hard* (Theoretical Computer Science, 2024): their Theorem 1, that perfect matching cut is NP-hard on 3-connected cubic bipartite planar graphs, and the construction in its proof supply all of the hardness, and their proof in turn uses Andreas Darmann and Janosch Döcker's hard variant of not-all-equal satisfiability.

Paola T. Pantoja, Simone Dantas and Atílio G. Luiz also studied graceful colorings of subcubic graphs, proving graceful 5-coloring hard on cubic planar graphs and graceful 4-coloring hard on graphs of maximum degree three; the first step of our proof, that a vertex with three neighbors gets color 1 or 4, is a case of a lemma of theirs. The equivalence is formalized with Lean 4 and Mathlib. [Further credits and source notes](checks/README.md) give the exact references and the sources that could not be read in full.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamPlanarGracefulColoring2026,
  author = {Graham, P.},
  title = {{Graceful 4-coloring of planar graphs is NP-complete}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/planar-graceful-coloring-v1/results/planar-graceful-coloring}}
}
```
