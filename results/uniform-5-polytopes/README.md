# The convex uniform 5-polytopes

[![Checks](https://github.com/6/clank-lab/actions/workflows/uniform-5-polytopes.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/uniform-5-polytopes.yml)

A [uniform polytope](https://en.wikipedia.org/wiki/Uniform_5-polytope)
looks the same at every vertex and has uniform facets, down to regular
polygons. Conway and Guy announced the four-dimensional list in 1965;
[Möller's 2004 dissertation](https://ediss.sub.uni-hamburg.de/handle/ediss/689)
gave a complete account of its proof. Schulte's 2017 survey stated that a complete list was known only in dimension
four; Winter's 2021 dissertation recorded the higher-dimensional
classification as open.

This work gives a computer-assisted completeness proof for the known convex
uniform 5-polytopes: Wythoff constructions of types $A_5$, $B_5$ and $D_5$, prisms over
convex uniform 4-polytopes, and products of regular polygons with convex
uniform polyhedra. These families overlap; the theorem asserts coverage,
not a disjoint count. It extends Möller's enumeration method and is
conditional on the cited three-dimensional classification, the
four-dimensional classification (Conway–Guy 1965, proved complete by Möller
2004), the written reductions and the certificate checkers. Lean checks
only a conditional implication and selected geometric lemmas. The explicit
premises have not been jointly instantiated in Lean; their connection to the
certificates remains external.

Computer-assisted; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23647462](https://doi.org/10.5281/zenodo.23647462)

## Check it

With Python 3.11 or later, Bash 4.4 or later and the dependencies in
[checks/requirements.txt](checks/requirements.txt) installed, run from this
directory (about half an hour):

```sh
PYTHON=python3 bash checks/verify-public.sh full
```

A successful run ends with `uniform-5-polytopes public full: PASS`.
[checks/README.md](checks/README.md) has installation instructions, the
scope of the checks and a shorter partial check. The
[detailed checking notes](checks/checking-notes.pdf), their
[LaTeX source](checks/edition-details.tex) and the
[section and statement reference map](checks/edition-reference-map.md)
retain the supporting derivations and the earlier section locators.

## Credits

Möller's [Vierdimensionale Archimedische Polytope](https://ediss.sub.uni-hamburg.de/handle/ediss/689) and [4-dimensionale Archimedische Polytope](https://doi.org/10.1007/BF03322887) are the direct methodological foundation: edge-neighborhood enumeration, forced-radius comparison and vertex-neighborhood completion. The proof uses the three-dimensional classification recorded in Schulte's [Symmetry of polytopes and polyhedra, §18.5](https://web.archive.org/web/20240415194537/https://www.csun.edu/~ctoth/Handbook/chap18.pdf) and the four-dimensional classification announced by Conway and Guy and proved complete by Möller.

Theorem 3.1 in Berestovskii and Nikonorov's [On m-point homogeneous polytopes in Euclidean spaces](https://doi.org/10.2298/FIL2325405B) proves the Separation lemma's nearest-vertex adjacency statement. M. Càllisto's [The 28 convex uniform honeycombs: a completeness theorem](https://doi.org/10.5281/zenodo.22881686) provides a methodological precedent for dividing verification between Lean arguments and external finite certificate checks. The manuscript also credits the Lean and Mathlib contributors and the arithmetic and numerical libraries used by the checkers.

The checking documentation also gives further credits and source notes.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamUniform5Polytopes2026,
  author       = {Graham, P.},
  title        = {{The convex uniform 5-polytopes: a computer-assisted classification}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/uniform-5-polytopes-v5/results/uniform-5-polytopes}},
  doi          = {10.5281/zenodo.23647462}
}
```
