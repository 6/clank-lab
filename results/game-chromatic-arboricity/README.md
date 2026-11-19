# Monotone classes of bounded game chromatic number have bounded arboricity

[![Checks](https://github.com/6/clank-lab/actions/workflows/game-chromatic-arboricity.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/game-chromatic-arboricity.yml)

In the [graph coloring game](https://en.wikipedia.org/wiki/Graph_coloring_game), Alice and Bob take turns coloring the vertices of a graph from a fixed set of $k$ colors, never giving two adjacent vertices the same color. Alice moves first and wins if every vertex gets colored; Bob wins if some uncolored vertex ends up with all $k$ colors among its neighbors. The game chromatic number of a graph is the least $k$ with which Alice can force a win. In [1999](https://doi.org/10.1006/jctb.1998.1878) Xuding Zhu asked, as his Question 3, whether every class of graphs that is closed under taking subgraphs and has bounded game chromatic number must have bounded [arboricity](https://en.wikipedia.org/wiki/Arboricity), that is, whether the edges of its graphs split into a bounded number of forests. We prove that it must. More precisely, for every $K$ there is $d$ such that every graph of average degree at least $d$ has a subgraph on which Bob wins with any number of colors up to $K$. The proof builds on the theorem of Daniela Kühn and Deryk Osthus that every graph of large enough average degree contains a subgraph of large average degree with no cycle of length 4.

Zhu's Question 2 asks the same with the game coloring number in place of the arboricity. It has a negative answer from 2001: an example of Hal Kierstead and William Trotter, together with a bound of Thomas Dinski and Zhu, gives a class closed under subgraphs with game chromatic number at most 12 and unbounded game coloring number. Zhu's Question 4, the conjecture of Dinski and Zhu that such classes have bounded acyclic chromatic number, remains open.

Written proof, with Lean and computer checks; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.24376624](https://doi.org/10.5281/zenodo.24376624)

## Check it

Install [elan](https://github.com/leanprover/elan) and Git. From `lean/`, run:

```sh
lake exe cache get
lake build
```

The first command downloads Mathlib's compiled files. The build then checks the proof, the exact statements and the axioms used, in about a minute with under 8 GB of memory. The theorem of Kühn and Osthus is assumed, as the explicit hypothesis `C4FreeSubgraphTheorem` of both main theorems; everything else is proved. The [Lean notes](lean/README.md) give the definitions, how they match the paper and where each lemma is proved.

## Credits

Xuding Zhu posed the question as Question 3 of *The game coloring number of planar graphs* (Journal of Combinatorial Theory, Series B, 1999). The proof rests above all on Theorem 1 of Daniela Kühn and Deryk Osthus, *Every graph of sufficiently large average degree contains a C4-free subgraph of large average degree* (Combinatorica, 2004), which gives subgraphs of girth at least six; Richard Montgomery, Alexey Pokrovskiy and Benny Sudakov gave an explicit bound in *C4-free subgraphs with large average degree* (Israel Journal of Mathematics, 2021). Bob's strategy adapts the weighting argument of Paul Erdős and John Selfridge, *On a combinatorial game* (Journal of Combinatorial Theory, Series A, 1973), and of József Beck's criterion for Maker–Breaker games in *Van der Waerden and Ramsey type games* (Combinatorica, 1981), as stated in Michael Krivelevich's survey *Positional games* (Proceedings of the ICM, 2014).

The negative answer to Zhu's Question 2 combines Example 6.1 of Hal Kierstead and William Trotter's *Competitive colorings of oriented graphs* (Electronic Journal of Combinatorics, 2001) with the bound of Thomas Dinski and Xuding Zhu in *A bound for the game chromatic number of graphs* (Discrete Mathematics, 1999), where Question 4 was first posed as a conjecture. Zdeněk Dvořák's 2007 doctoral thesis reduces that conjecture to a question on subdivided graphs. The formalization uses Lean 4 and Mathlib.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamGameChromaticArboricity2026,
  author = {Graham, P.},
  title = {{Monotone classes of bounded game chromatic number have bounded arboricity}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/game-chromatic-arboricity-v1/results/game-chromatic-arboricity}},
  doi          = {10.5281/zenodo.24376624}
}
```
