# Independent certificate check

Run `python3 -I checks/check.py` from the result folder with Python 3.10 or
later. The check uses only the standard library and finishes in seconds.
`python3 -I checks/check.py --list` lists its steps.

The interval $I$ is the exact height interval specified in the
[Lean guide](../lean/README.md). Its endpoints are inputs to the checker;
existence and uniqueness of a root inside it are proved by Lean.

The Python checker is an independent implementation of the arithmetic checks for the same rational three-point certificate used by Lean. It reconstructs the polynomial operators and factor-matrix products, checks all 274 residual coefficients and their total absolute error, and bounds the candidate energy over $I$. It also rejects eight deliberately corrupted certificates. It does not re-prove the global geometric classification or local uniqueness: those are Lean obligations. The detailed global and local argument is in the [Lean guide](../lean/README.md).

The separate rigorous enclosure is $32.716949460147 < E(p) < 32.716949460149$, giving $32.71694946\ldots$. [`energy_enclosure.py`](energy_enclosure.py) checks it only in Python, by rational interval arithmetic on all 45 pair distances over $I$, with outward integer-square-root bounds at precision $2^{-420}$. The existence and uniqueness of the height root are Lean facts; Python encloses the energy over the entire interval without solving that root. This enclosure is supplementary and is not part of the Lean theorem.

## Certificate sizes and finite classification

The three-point certificate has 20 nonzero matrix blocks, 42,950 factor entries and 274 residual coefficients; [`certificate.json.gz`](../data/certificate.json.gz) is 1,246,399 bytes (2,670,249 bytes expanded). The window classification checks 84 anchor records, of which 43 are eligible, and nine seven-clique witnesses, all yielding the same pattern. Its exact data occupy 14,992 bytes. These are certificate sizes and finite classification counts, not a discretization of the continuum of competitors.

The scalar, window-classification, and constrained-Hessian certificates are
exact data embedded in the corresponding Lean modules. Lake expands the
large compressed ambient certificate automatically before checking it.

## The figure

[`draw_antiprism.py`](draw_antiprism.py) draws [`antiprism.svg`](../data/antiprism.svg) and [`antiprism.pdf`](../data/antiprism.pdf) from the Lean definition of the candidate, `lean/ThomsonN10/Candidate.lean`: its rational height interval and the coordinates of `candidateAt`. Run it with `--check` to check the supplied files without overwriting them. The check reads the drawing back, recovers each point's three coordinates from its two views, and requires them to be the candidate's point with the same index, to within $10^{-6}$ of the radius; it also checks the hull edges, the marks for $h$ and $\pi/4$, and the labels. `check.py` runs it and confirms that the six controls in [`data/controls/`](../data/controls/) (two points nudged by 0.001 typographic points, a pole moved by one, two swapped labels, a missing edge and a shifted height mark) are rejected. The figure is an illustration, not part of the proof.

## Formal correspondence

The [formal definitions and checking details](formal-correspondence.md)
identify the fixed coefficient data, formal theorem names and local
perturbation estimates, and retain the implementation and attribution
notes relocated from the paper. This includes the exact source mappings
for the energy polynomial, candidate upper bound, Gram-stability estimates,
orthogonal alignment and pair remainder inequality.

## Further credits

- Aravind Karthigeyan, [thomson-n9-lean](https://github.com/aravindkarthigeyan/thomson-n9-lean) — most of the MIT-licensed Lean code and the proof design.
- Jingxing Huang, [Thomson n=9 proof and manuscript](https://doi.org/10.5281/zenodo.23573472) — related nine-point candidate.
- Jingxing Huang, [ten-point stationarity continuation](https://github.com/Stickerbug/thomson-n9-proof/blob/fce398ce69c369a8de5b10d194af137cf33edd54/proof_work/publication_validation/formal/ThomsonCertificate/N10StationarityRightTerm3Final.lean) — related endpoint-sign theorem `d4dStationarity_right_endpoint_positive`.
- L. Föppl, [Stabile Anordnungen von Elektronen im Atom](https://doi.org/10.1515/crll.1912.141.251) — candidate history.
- V. A. Yudin, [Minimum potential energy of a point system of charges](https://doi.org/10.1515/dma.1993.3.1.75) — energy-bound background.
- R. E. Schwartz, [The Five-Electron Case of Thomson's Problem](https://arxiv.org/abs/1001.3702) — preceding exact case.
- N. N. Andreev, [An extremal property of the icosahedron](https://zbmath.org/0877.51021) — preceding exact case.
- H. Cohn and A. Kumar, [Universally optimal distribution of points on spheres](https://arxiv.org/abs/math/0607446) — energy-minimization background.
- Hung Tran, [A Lean Proof of the Thomson Problem for Seven Electrons](https://www.vals.ai/blogs/thomson-n7-lean-proof) — related formal proof.
- L. Kryvonos, L. Liehr and M. A. Taylor, [Energy minimization for eight points on the sphere](https://arxiv.org/abs/2609.22077) — related eight-point result.
- Joseph Tooby-Smith and Alex Zughaid, [A warrant for the N=8 Thomson problem, in Lean 4](https://github.com/jstoobysmith/Thomson-N-8-Warrant) — related formalization.
- Alex Zarco, [Five points on the sphere](https://github.com/alejandrozarco/five-points-riesz) — related Riesz certificates and formalizations.
- Alex Zarco, [`The pentagonal bipyramid as the unique logarithmic-energy minimiser for seven points on the sphere`](https://doi.org/10.5281/zenodo.23086382) — related logarithmic-energy warrant.
- P. Delsarte, J. M. Goethals and J. J. Seidel, [Spherical codes and designs](https://doi.org/10.1007/BF03187604) — bound framework.
- C. Bachoc and F. Vallentin, [New upper bounds for kissing numbers from semidefinite programming](https://arxiv.org/abs/math/0608426) — three-point bound framework.
- H. Cohn and J. Woo, [Three-point bounds for energy minimization](https://arxiv.org/abs/1103.0485) — energy-bound framework.
- saberwatchmanga (formerly terry2418), [Lean-verified local minimality for ten charges on a sphere](https://github.com/saberwatchmanga/-lean-finite-certificates/tree/main/Thomson10LocalMinimum) — concurrent local result.
- saberwatchmanga (formerly terry2418), [A Lean-checked distance restriction for ten charges on a sphere](https://github.com/saberwatchmanga/-lean-finite-certificates/tree/main/Thomson10Chord1935) — concurrent distance restriction.
- T. Erber and G. M. Hockney, [Equilibrium configurations of N equal charges on a sphere](https://doi.org/10.1088/0305-4470/24/23/008) — numerical background.
- D. J. Wales and S. Ulker, [Cambridge Cluster Database: Thomson problem](https://www-wales.ch.cam.ac.uk/~wales/CCD/Thomson/table.html) — numerical configurations.

## Sources used during development

The source scope and development account below is retained from the landing page. The short credit account is in the [result README](../README.md#credits).

Aravind Karthigeyan's pinned October 6, 2026 [README](https://github.com/aravindkarthigeyan/thomson-n9-lean/blob/168ff0c98cab4dfda0460ba55f8d169070ac385e/README.md) states “global optimality and uniqueness for nine distinct points” and calls the project “a research release requesting external review”. That AI-generated proof establishes the D3h tricapped trigonal prism as minimizer, with equality up to orthogonal transformation and permutation. We reuse most of its MIT-licensed Lean code and follow its proof design. [THIRD_PARTY.md](../THIRD_PARTY.md) preserves the file-level attribution, changes and full license notice.

Jingxing Huang's later ten-point continuation includes
[`d4dStationarity_right_endpoint_positive`](https://github.com/Stickerbug/thomson-n9-proof/blob/fce398ce69c369a8de5b10d194af137cf33edd54/proof_work/publication_validation/formal/ThomsonCertificate/N10StationarityRightTerm3Final.lean),
a Lean theorem giving the positive sign of the stationarity expression at
a rational right endpoint for the one-parameter D4d candidate family.
This is a partial result; the accompanying
[status record](https://github.com/Stickerbug/thomson-n9-proof/blob/fce398ce69c369a8de5b10d194af137cf33edd54/proof_work/publication_validation/N10_CONTINUATION_STATUS_2026-10-25_zh.md)
does not claim global ten-point minimality. We use no results, code or data
from this ten-point continuation.

Alex Zarco's *Five points on the sphere* (<https://github.com/alejandrozarco/five-points-riesz>) reports AI-produced, unreviewed five-point Riesz certificates and Lean formalizations of results already known from Schwartz. We use no code or theorem from this work.

The prior and concurrent credits remain in [historical context](../checks/context.md), including Föppl; Yudin; Schwartz; Andreev; Cohn and Kumar; Hung Tran; Kryvonos, Liehr and Taylor; Joseph Tooby-Smith and Alex Zughaid; Alex Zarco; Delsarte, Goethals and Seidel; Bachoc and Vallentin; Cohn and Woo; saberwatchmanga (formerly terry2418); Erber and Hockney; and the Cambridge Cluster Database. That account also preserves the shared-cutoff provenance qualification. No priority claim is made.

Jingxing Huang also reports a separate nine-point Lean proof candidate with conditional independent Python checking ([repository, revision of October 25, 2026](https://github.com/Stickerbug/thomson-n9-proof/tree/5f8492931e40e62e2064a162f978ff0e2541a2f6), [Zenodo record 23573472](https://doi.org/10.5281/zenodo.23573472)).
