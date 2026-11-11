# The Heawood family is not the complete list of excluded minors for Colin de Verdière invariant at most 5

[![Checks](https://github.com/6/clank-lab/actions/workflows/heawood-family-mu5.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/heawood-family-mu5.yml)

The [Colin de Verdière invariant](https://en.wikipedia.org/wiki/Colin_de_Verdi%C3%A8re_graph_invariant) $\mu(G)$ of a graph is a number defined from the matrices that have the graph's adjacency pattern. It captures topology: $\mu(G) \le 3$ exactly when $G$ is planar, and $\mu(G) \le 4$ exactly when $G$ can be embedded in space with no two cycles linked. For each $k$ the graphs with $\mu \le k$ are characterized by a finite list of excluded minors. For $k = 4$ the list is the [Petersen family](https://en.wikipedia.org/wiki/Petersen_family), seven graphs obtained from $K_6$ and $K_{3,3,1}$ by $\Delta Y$- and $Y\Delta$-transformations. The [Heawood family](https://en.wikipedia.org/wiki/Heawood_family) consists of the 78 graphs obtained in the same way from $K_7$ and $K_{3,3,1,1}$, all with $\mu = 6$. Hein van der Holst proposed in 2006 that the Heawood family is the complete list of excluded minors for $\mu \le 5$; Thomas Mattman and Andrei Pavelescu stated this as Conjecture 4 of [arXiv:2607.01414](https://arxiv.org/abs/2607.01414) (2026) and derived from it that three intrinsically knotted graphs with 23 edges have $\mu = 5$.

We show that two of those three graphs, with 11 and 12 vertices, have $\mu = 6$ and no minor in the Heawood family. So the Heawood family is not the complete list of excluded minors for $\mu \le 5$. More precisely, either their common minor $H$, a 4-regular graph with 11 vertices and 22 edges, is an excluded minor, or both of the two graphs are. As a corollary, two conjectures of van der Holst about [4-flat graphs](https://arxiv.org/abs/2408.12681) cannot both hold: that a graph is 4-flat exactly when $\mu \le 5$, and that the Heawood family is the complete list of excluded minors for 4-flatness.

Computer-assisted; not yet reviewed by experts.

The proofs, the computer checks and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

The two graphs are in `data/graphs.g6`, and `data/G1-cert.json` and `data/G2-cert.json` each give a matrix that proves $\mu \ge 6$. With Python 3.12 or later, from this folder:

```sh
python3 -m pip install --require-hashes -r checks/requirements.txt
sh checks/check.sh
```

It takes about half a minute on one core and ends with three lines starting `PASS: mu(G1) >= 6 and mu(G2) >= 6, and neither has a Heawood-family minor`. It checks both certificates with two separately written checkers, confirms that corrupted certificates are rejected, regenerates the Heawood family twice, searches both graphs for Heawood-family minors in two ways, checks the apex structure used in the paper, and checks that the paper's figure is drawn from the data. The [checker documentation](checks/README.md) describes each program and the certificate format.

## Credits

Hein van der Holst proposed the Heawood family as the excluded minors for $\mu \le 5$, in *Graphs and obstructions in four dimensions* (Journal of Combinatorial Theory, Series B, 2006), where van der Holst proved that its graphs are not 4-flat. Thomas Mattman and Andrei Pavelescu stated the conjecture and the prediction we test (arXiv, 2026); the two graphs are entries 90 and 332 of their Appendix A. Hyoungjun Kim and Thomas Mattman found the two graphs and showed that every graph obtained from either by deleting or contracting one edge is 2-apex except $H$ (Discrete Applied Mathematics, 2025). Thomas Mattman and Mike Pierce found $H$ and showed that it is minor-minimal among graphs that are not 2-apex (Contemporary Mathematics, 2017). Agelos Georgakopoulos and Martin Winter traced van der Holst's conjectures and proved that every Heawood graph is an excluded minor for 4-flatness (arXiv, 2024). The invariant is Yves Colin de Verdière's; the facts about it used here are from the survey of van der Holst, László Lovász and Alexander Schrijver.

The certificates use the Schur complement and Krawczyk's interval test in the form of Ramon Moore's existence theorem. The checkers use NetworkX, mpmath, python-flint (FLINT) and NumPy. [Further credits](checks/README.md#further-credits) give the exact references.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamHeawoodFamilyMu52026,
  author = {Graham, P.},
  title = {{The Heawood family is not the complete list of excluded minors for Colin de Verdière invariant at most 5}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/heawood-family-mu5-v1/results/heawood-family-mu5}}
}
```
