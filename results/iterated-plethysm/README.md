# Symmetry of hook+column coefficients in iterated plethysms

[![Checks](https://github.com/6/clank-lab/actions/workflows/iterated-plethysm.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/iterated-plethysm.yml)

[Plethysm](https://en.wikipedia.org/wiki/Plethysm) describes composition of symmetric functions, which encode representations and counting problems. Expanding a plethysm in [Schur functions](https://en.wikipedia.org/wiki/Schur_polynomial) produces coefficients indexed by partitions. Gutiérrez and Rosas asked in their [2022 preprint](https://arxiv.org/abs/2201.00240v2) whether the coefficients at hook+column partitions form symmetric sequences for every iterated plethysm of complete homogeneous functions. This work answers their Question 1 affirmatively, building on their signed-alphabet method and earlier formulas of Langley and Remmel.

More generally, for every homogeneous rational symmetric function $`g`$ of degree $`d\geq1`$ and every integer $`a\geq2`$, put $`N=ad`$. If $`b(\beta,\gamma)`$ is the coefficient of $`s_{(N-2\beta-\gamma,2^\beta,1^\gamma)}`$ in $`g[h_a]`$, with the paper's shape convention and zero for invalid shapes, then $`b(\beta,\gamma)=b(d-1-\gamma-\beta,\gamma)`$ for every integer $`\beta`$ and every $`\gamma\geq0`$. The coefficients vanish when $`\beta+\gamma\geq d`$, and the column coefficient is zero. For every nonempty list of positive integers $`n_1,\ldots,n_k`$, the resulting sequences for $`h_{n_1}\circ\cdots\circ h_{n_k}`$ are palindromic after zero entries are removed; the paper also gives the reflection with zeros retained.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Install Lean through [elan](https://github.com/leanprover/elan). From this folder, run:

```sh
cd lean
lake exe cache get
lake build
```

The first command downloads the mathematical library's compiled cache and needs an internet connection. Allow several minutes for installation and downloading, then about two minutes for the proof build, with about 8 GB of memory. The [Lean notes](lean/README.md) describe the definitions, dependencies, theorem checks, and examples.

## Credits

Álvaro Gutiérrez and Mercedes H. Rosas posed Question 1 in *Partial symmetries of iterated plethysms*, following Conjecture 1 of Gutiérrez's thesis. Their Theorems 2.15 and 2.16 give formulas for two three-factor families, and Theorem 2.19 shows that the second symmetric and exterior plethysms $`s_{(2)}[f]`$ and $`s_{(1,1)}[f]`$ of a Schur-positive $`f`$ preserve flip-symmetry, a stronger form of the symmetry. Their Lemma 3.8 and the specialization at the signed alphabet $`1-x-y`$ supply the central tools used here. The additional step is to apply reciprocal substitution to the specialized plethysm for an arbitrary homogeneous outer function.

Thomas M. Langley and Jeffrey B. Remmel's Theorem 4.8 gives the two-factor hook+column formula underlying those families. Gutiérrez's thesis also proves the symmetry-preservation result in Theorem 4.28; Gutiérrez and Rosas's positivity paper gives the general signed-alphabet vanishing criterion in Lemma 3.1, and its Theorem 5.1 already implies that the column coefficient vanishes. Newton's identities and the Jacobi–Trudi determinant provide the definitions used in the proof. Lean and the Mathlib library check the algebraic argument, the existence and uniqueness of Schur expansions, and the passage to iterated plethysms. The paper gives precise references and explains how the formal statements match the coefficient sequences.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamIteratedPlethysm2026,
  author = {Graham, P.},
  title = {{Symmetry of hook+column coefficients in iterated plethysms}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/iterated-plethysm-v1/results/iterated-plethysm}}
}
```
