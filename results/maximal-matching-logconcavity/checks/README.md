# Exact computation

Run the command in the result's README from the result folder. Python 3.10 or later is sufficient; [requirements.txt](requirements.txt) has no third-party dependencies. The computation uses exact integers throughout and needs no network or external files. A measured complete invocation took 0.04 seconds and about 38 MiB of peak memory; timings depend on the machine.

The [certificate](../data/graph.json) contains 76 adjacency rows as hexadecimal bit masks, all 39 coefficients as decimal strings, and the independent-set counts. Bit j of row i records adjacency of vertices i and j. Vertices 0 through 11 form the edges (0,1), (2,3), …, (10,11); vertices 12 through 43 and 44 through 75 form the cliques. All edges between the first part and the cliques are present. No edges connect the two cliques.

The cover keys A:0 through A:6 count independent sets of each size in the six-edge part, including the empty set. B:1 and B:2 count the nonempty independent sets in the union of the cliques. In particular, the 428 odd independent sets are counted even though their complements have no perfect matching.

The one entry point contains two separate counting implementations. The factorial formula sums over the chosen internal edges and the injections into the cliques. The other enumerates labeled independent sets from the supplied adjacency and uses a vertex-pairing recurrence on the residual graph. Both compare the entire coefficient vector and cover with the certificate before testing the inequality. The second implementation does not call the first one's counting routines.

Small-graph comparisons replace both cliques by cliques of order two and four. A third, generic calculation uses actual vertex subsets and no compressed residual states. It also reproduces the known polynomials for a single edge, a four-vertex path, a four-vertex clique and the complete bipartite graph with parts of size two and three. Corruption tests alter one adjacency bit, the coefficient at size 36, and an odd independent-set count. The adjacency check rejects the altered edge before counting; each counting method rejects the altered coefficient and odd-set count. The generic calculation checks the residual reductions, using the uncovered-set identity proved in the paper.

These checks support the written reductions in the paper. They do not constitute proof-assistant verification of either the reductions or the Python implementation. The SVG and the paper's schematic display the three parts of the certified graph; the thick connections represent complete joins, not single edges.

The paper can be built with a TeX distribution providing pdfLaTeX, Latin Modern, AMS packages, geometry, hyperref, booktabs and PGF/TikZ. Run pdfLaTeX twice on the source to resolve its references, directing temporary build files outside the paper folder.

## Further credits

The principal credits to Tomislav Došlić, Taylor Short and Ivana Zubac are in the result's README and paper. The following work provides nearby mathematical context; its results are not used as premises of the counterexample.

- Matt Burnham and Aysel Erey, [On the roots of maximal matching polynomials](https://doi.org/10.1016/j.disc.2025.114547), Discrete Mathematics 348 (2025), 114547. The accessible publisher preview includes real-rootedness statements for paths (Corollary 3.1), cycles (Theorem 7), and broom trees (Corollary 7.1). The full text was unavailable; we do not use its truncated concluding sentence as evidence of open status.
- Hanlin Chen, Guihua Huang and Sijia Lei, [The Maximal Matching Polynomial of Hexacyclic Systems](https://doi.org/10.46793/match.97-2.14426), published online August 26, 2026, MATCH 97 (2027), 621–638. Theorem 2.1 gives a transfer-matrix formula for that family. Our graph is outside that family, and our computation uses no transfer-matrix result from the paper.
- Hanlin Chen and Yuwan Zhang, [Maximal matching polynomials of phenylene and benzenoid chains](https://doi.org/10.2298/FIL2533981C), Filomat 39 (2025), 11981–11996, on another molecular-graph setting for these polynomials.
- Chengqi Li, Jinhui Yin and Lingjuan Shi, [The number of maximal matchings in polygon rings](https://arxiv.org/abs/2506.08687), and Lingjuan Shi, Wei Li and Kai Deng, [On the maximal matchings of trees](https://arxiv.org/abs/2506.08557), both posted June 10, 2025, on enumeration in their respective graph families.
- Kai Zhang, [Upper bounds for the average size of maximal matchings in bicyclic graphs](https://arxiv.org/abs/2608.06818v1), posted August 7, 2026. Its extremal average-size question differs from the coefficient inequality addressed here.
- Benjamin Hellouin de Menibus and Takeaki Uno, [Maximal Matching and Path Matching Counting in Polynomial Time for Graphs of Bounded Clique Width](https://doi.org/10.1007/978-3-642-20877-5_47), COCOON 2011, Theorem 1. Counting on graph classes of this kind is established prior work; the contribution here is the explicit negative answer to the coefficient question.

The implementations use [Python](https://www.python.org/); the paper uses [LaTeX](https://www.latex-project.org/) and [PGF/TikZ](https://ctan.org/pkg/pgf). No third-party source code or figures are included.
