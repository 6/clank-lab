# The Thomson problem for N = 10

[![Checks](https://github.com/6/clank-lab/actions/workflows/thomson-10.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/thomson-10.yml)

For ten equal charges on a sphere, does the bicapped square antiprism minimize Coulomb energy? This is the ten-point case of the [Thomson problem](https://en.wikipedia.org/wiki/Thomson_problem), associated with J. J. Thomson's 1904 atomic model. We adapt the MIT-licensed formal code of [Aravind Karthigeyan's nine-point project](https://github.com/aravindkarthigeyan/thomson-n9-lean/tree/168ff0c98cab4dfda0460ba55f8d169070ac385e). We prove global optimality among all ten distinct unit-sphere points, with equality exactly up to orthogonal maps (including reflections) and relabeling.

![The bicapped square antiprism: a side view with the heights h of the two squares marked, and the view from above, where the lower square is the upper one turned by π/4 (illustration only; not part of the proof).](data/antiprism.svg)

The candidate's height is specified by an exact equation. Lean proves that the height exists and is unique in its specified interval, that the candidate consists of distinct unit vectors, and that every competitor has at least its energy, with equality exactly for congruent configurations. No symmetry is assumed of competitors. The proof first localizes every competitor of no greater energy, then uses orthogonal alignment and a local energy bound covering all spherical perturbations to force equality with the candidate.

The new inputs are the ten-point energy, interval-classification and Hessian certificates. The hardest step is the three-point energy certificate, whose error must be small enough to force geometric localization. The [paper](paper/paper.pdf) states the result and proof overview in three pages; its appendices keep the complete mathematical argument.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23591086](https://doi.org/10.5281/zenodo.23591086)

## Check it

Install [elan](https://github.com/leanprover/elan) and Python 3.10 or later. From this folder:

```sh
cd lean
lake exe cache get
lake build
cd ..
python3 -I checks/check.py
```

The Python checker independently implements checks of the same rational certificates and rejects eight corruptions; it also checks that the figure shows the candidate's points. Lean proves the geometric and analytic obligations. Python also checks a separate rigorous enclosure of the candidate energy $E$, $32.716949460147 < E < 32.716949460149$, outside the Lean theorem. The [Lean guide](lean/README.md) and [checking guide](checks/README.md) give the exact height interval, theorem hypotheses, axioms, certificate sizes, dependency versions, memory requirements and qualified build timing.

## Credits

Aravind Karthigeyan's pinned October 6, 2026 [README](https://github.com/aravindkarthigeyan/thomson-n9-lean/blob/168ff0c98cab4dfda0460ba55f8d169070ac385e/README.md) states “global optimality and uniqueness for nine distinct points” and calls the project “a research release requesting external review”. We substantially adapt its MIT-licensed Lean code and proof design. [THIRD_PARTY.md](THIRD_PARTY.md) preserves the file-level attribution, changes and full license notice.

The prior and concurrent credits remain in [historical context](checks/context.md), including Föppl; Yudin; Schwartz; Andreev; Cohn and Kumar; Hung Tran; Kryvonos, Liehr and Taylor; Joseph Tooby-Smith and Alex Zughaid; Alex Zarco; Delsarte, Goethals and Seidel; Bachoc and Vallentin; Cohn and Woo; saberwatchmanga (formerly terry2418); Erber and Hockney; and the Cambridge Cluster Database. That account also preserves the shared-cutoff provenance qualification. No priority claim is made.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamThomson102026,
  author       = {Graham, P.},
  title        = {{The Thomson problem for N = 10}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/thomson-10-v5/results/thomson-10}},
  doi          = {10.5281/zenodo.23591086}
}
```
