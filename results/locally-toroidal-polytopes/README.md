# Existence of locally toroidal regular 4-polytopes

[![Checks](https://github.com/6/clank-lab/actions/workflows/locally-toroidal-polytopes.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/locally-toroidal-polytopes.yml)

A [locally toroidal regular 4-polytope](https://en.wikipedia.org/wiki/Abstract_regular_polytope) is an abstract polytope whose facets and vertex-figures are maps on tori. Peter McMullen and Egon Schulte developed their classification; Egon Schulte and Asia Ivić Weiss asked in [Problem 16 (2006)](https://arxiv.org/abs/math/0608397) whether the remaining family exists and how its groups can be classified. This work proves the existence half of that problem and of McMullen–Schulte's 2002 Conjecture 10C7: the universal regular 4-polytope $\{\{4,4\}_{(s,0)},\{4,4\}_{(u,0)}\}$ exists for every pair of distinct odd integers $s,u\geq3$, with no gcd restriction. Here $\{4,4\}_{(s,0)}$ is the square grid wrapped onto a torus with period $s$ in both directions. Finiteness and group classification remain open.

McMullen–Schulte's book records the finite example with periods 3 and 5 and its dual. This theorem gives existence for every distinct odd pair, including pairs sharing a factor. The hardest new step proves that the facet and vertex-figure groups overlap exactly in their common dihedral subgroup, using a commutator argument that allows independent periods. The classical toroidal presentations and the correspondence between groups and regular polytopes are reused.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23562182](https://doi.org/10.5281/zenodo.23562182)

![Square-torus fundamental domains of periods 3 and 9, with matching arrows on opposite sides](data/local-toroids.svg)

Facet and vertex-figure maps for the theorem's example with periods 3 and 9. Identify opposite sides following the matching arrows; repeated boundary points become the same torus vertices. The shaded square, thick edge and dot form a base flag. The drawing is generated from modular grid data and checked against the vertex, edge and square definition of these maps.

## Check it

Install [elan](https://github.com/leanprover/elan), the standard Lean toolchain manager, and Git. From this folder:

```sh
cd lean
lake exe cache get
lake build
```

The project selects its Lean version automatically. The build checks the theorem, the geometric torus identification, the universal polytope construction, and the axiom guards. See [the Lean guide](lean/README.md) for the theorem statements.

## Credits

The proof builds on Peter McMullen and Egon Schulte's theory of abstract regular polytopes and H. S. M. Coxeter and W. O. J. Moser's presentations of toroidal maps. Egon Schulte and Asia Ivić Weiss formulated the classification problem. The earlier finite example with periods 3 and 5 and its dual are recorded in McMullen–Schulte's book, which credits G. Havas's coset enumeration and Leytem's group identification. Barry Monson and Egon Schulte developed related constructions over finite fields. Maria Elisa Fernandes and Claudio Alexandre Piedade studied faithful permutation representations of toroidal maps and regular polytopes of type $\{4,4,4\}$. The paper gives the references and distinguishes these results from the existence theorem proved here. The Lean project uses Lean and Mathlib.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamLocallyToroidalPolytopes2026,
  author       = {Graham, P.},
  title        = {{Existence of locally toroidal regular 4-polytopes}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/locally-toroidal-polytopes-v1/results/locally-toroidal-polytopes}},
  doi          = {10.5281/zenodo.23562182}
}
```
