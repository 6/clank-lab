# The convex uniform 5-polytopes

[![Checks](https://github.com/6/clank-lab/actions/workflows/uniform-5-polytopes.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/uniform-5-polytopes.yml)

A [uniform polytope](https://en.wikipedia.org/wiki/Uniform_5-polytope)
looks the same at every vertex and has uniform facets, down to regular
polygons. Conway and Guy announced the four-dimensional list in 1965;
[Möller's 2004 dissertation](https://ediss.sub.uni-hamburg.de/handle/ediss/689)
gave a complete account of its proof. Schulte (2017) and Winter (2021)
recorded the five-dimensional case as open.

This work gives a computer-assisted completeness proof for the known convex
uniform 5-polytopes: Wythoff constructions of types $A_5$, $B_5$ and $D_5$, prisms over
convex uniform 4-polytopes, and products of regular polygons with convex
uniform polyhedra. These families overlap; the theorem asserts coverage,
not a disjoint count. It extends Möller's enumeration method and is
conditional on the cited three-dimensional classification, the
four-dimensional classification (Conway–Guy 1965, proved complete by Möller
2004), the written reductions and the certificate checkers. Lean checks
only a conditional implication and selected geometric lemmas.

Computer-assisted; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23502450](https://doi.org/10.5281/zenodo.23502450)

## Check it

With Python 3.11 or later, Bash 4.4 or later and the dependencies in
[checks/requirements.txt](checks/requirements.txt) installed, run from this
directory (about half an hour):

```sh
PYTHON=python3 bash checks/verify-public.sh full
```

A successful run ends with `uniform-5-polytopes public full: PASS`.
[checks/README.md](checks/README.md) has installation instructions, the
scope of the checks and a shorter partial check.

## Credits

Möller's edge-neighborhood enumeration, forced-radius comparison and
vertex-neighborhood completion are the direct methodological foundation
([dissertation](https://ediss.sub.uni-hamburg.de/handle/ediss/689),
[*4-dimensionale Archimedische Polytope*](https://doi.org/10.1007/BF03322887)).
The proof uses the 3-D classification (see
[Schulte, §18.5](https://www.csun.edu/~ctoth/Handbook/chap18.pdf) and
[Grünbaum](https://doi.org/10.4171/EM/120)) and the 4-D classification of
Conway–Guy and Möller.
[Winter's 2021 dissertation, Appendix E.3](https://martinwintermath.github.io/pdf/phd/thesis.pdf)
states the open question of non-prismatic non-Wythoffian uniform polytopes
in dimension five or above.
[Càllisto's honeycomb work](https://doi.org/10.5281/zenodo.22881686) is a
methodological precedent for the division between Lean arguments and
external finite certificate checks.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamUniform5Polytopes2026,
  author       = {Graham, P.},
  title        = {{The convex uniform 5-polytopes: a computer-assisted classification}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/uniform-5-polytopes-v3/results/uniform-5-polytopes}},
  doi          = {10.5281/zenodo.23502450}
}
```
