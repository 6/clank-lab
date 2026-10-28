# The Thomson problem for N = 10

[![Checks](https://github.com/6/clank-lab/actions/workflows/thomson-10.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/thomson-10.yml)

For ten equal charges on a sphere, does the bicapped square antiprism minimize Coulomb energy? This is the ten-point case of the [Thomson problem](https://en.wikipedia.org/wiki/Thomson_problem), associated with J. J. Thomson's 1904 atomic model. We build directly on [Aravind Karthigeyan's AI-generated nine-point Lean proof](https://github.com/aravindkarthigeyan/thomson-n9-lean/tree/168ff0c98cab4dfda0460ba55f8d169070ac385e), reusing most of its MIT-licensed Lean code and its proof design. Jingxing Huang also reports [related nine-point work](https://doi.org/10.5281/zenodo.23573472). We prove global optimality among all ten distinct unit-sphere points, with equality exactly up to orthogonal maps (including reflections) and relabeling.

![The bicapped square antiprism: a side view with the heights h of the two squares marked, and the view from above, where the lower square is the upper one turned by π/4 (illustration only; not part of the proof).](data/antiprism.svg)

The candidate's height is specified by an exact equation. Lean proves that the height exists and is unique in its specified interval, that the candidate consists of distinct unit vectors, and that every competitor has at least its energy, with equality exactly for congruent configurations. No symmetry is assumed of competitors. The proof first localizes every competitor of no greater energy, then uses orthogonal alignment and a local energy bound covering all spherical perturbations to force equality with the candidate.

The new inputs are the ten-point energy, interval-classification and Hessian certificates. The hardest step is the three-point energy certificate, whose error must be small enough to force geometric localization. The [paper](paper/paper.pdf) contains the proof and its key lemmas in the main text; its appendices give routine verifications, finite case checks and formal-proof details.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23647395](https://doi.org/10.5281/zenodo.23647395)

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

Aravind Karthigeyan's [thomson-n9-lean](https://github.com/aravindkarthigeyan/thomson-n9-lean) supplies most of the MIT-licensed Lean code and the proof design. Jingxing Huang's [Thomson n=9 proof and manuscript](https://doi.org/10.5281/zenodo.23573472) is related nine-point work; Huang's [ten-point stationarity continuation](https://github.com/Stickerbug/thomson-n9-proof/blob/fce398ce69c369a8de5b10d194af137cf33edd54/proof_work/publication_validation/formal/ThomsonCertificate/N10StationarityRightTerm3Final.lean) proves the related endpoint-sign theorem `d4dStationarity_right_endpoint_positive`. L. Föppl's [Stabile Anordnungen von Elektronen im Atom](https://doi.org/10.1515/crll.1912.141.251) records the candidate's history.

The bound framework builds on P. Delsarte, J. M. Goethals and J. J. Seidel's [Spherical codes and designs](https://doi.org/10.1007/BF03187604), C. Bachoc and F. Vallentin's [New upper bounds for kissing numbers from semidefinite programming](https://arxiv.org/abs/math/0608426), and H. Cohn and J. Woo's [Three-point bounds for energy minimization](https://arxiv.org/abs/1103.0485). V. A. Yudin's [Minimum potential energy of a point system of charges](https://doi.org/10.1515/dma.1993.3.1.75) provides energy-bound background. The full work-by-work list, including preceding exact cases, numerical configurations and concurrent results, is in [Further credits](checks/README.md#further-credits).

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamThomson102026,
  author       = {Graham, P.},
  title        = {{The Thomson problem for N = 10}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/thomson-10-v8/results/thomson-10}},
  doi          = {10.5281/zenodo.23647395}
}
```
