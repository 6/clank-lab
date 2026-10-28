# A counterexample to the $\mathcal{E}$-derivation part of the LNED conjecture

[![Checks](https://github.com/6/clank-lab/actions/workflows/lned-counterexample.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/lned-counterexample.yml)

A [Mathieu–Zhao subspace](https://arxiv.org/abs/1701.05992v2) generalizes an ideal: if it contains every positive power of a polynomial, it must eventually contain those powers multiplied by any fixed polynomial. Wenhua Zhao's [LNED conjecture, posed in 2017](https://arxiv.org/abs/1701.05992v2), asks whether locally nilpotent derivations and E-derivations send every ideal to such a subspace. Zhao proved the ordinary-derivation case in one variable and several E-derivation cases, and supplied a Bernoulli-polynomial membership criterion. Specializing that criterion gives a counterexample over every characteristic-zero field $K$: for every nonzero $c$, the map $`\delta_c f(x)=f(x)-f(x+c)`$ sends the ideal $`(x(x-c/2))`$ to a subspace containing $x^{2m}$ and excluding $x^{2m+1}$ for every $m\ge1$. Thus the univariate E-derivation assertion is false. The formal proof also covers unit shifts in any chosen variable of a polynomial algebra. The ordinary-derivation assertion and the whole-image LFED conjecture remain unaffected.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23735733](https://doi.org/10.5281/zenodo.23735733)

## Check it

Install [elan](https://github.com/leanprover/elan), Git and a C/C++ toolchain. From this folder, run:

```sh
cd lean
lake exe cache get
lake build
```

The pinned Lean toolchain is installed through elan. The first command downloads library dependencies and their build cache; internet access is needed for that setup. The second checks the proofs, exact theorem statements and axiom restrictions. See the [checking guide](lean/README.md) for the definitions and additional rational-parameter results, and the [source notes](checks/README.md).

## Credits

- Wenhua Zhao, [Images of ideals under derivations and E-derivations of univariate polynomial algebras over a field of characteristic zero](https://arxiv.org/abs/1701.06125v1): the membership criterion specialized to obtain this counterexample.
- Wenhua Zhao, [Some open problems on locally finite or locally nilpotent derivations and E-derivations](https://arxiv.org/abs/1701.05992v2): the conjectures studied here.
- F. W. J. Olver et al. (eds.), [NIST Digital Library of Mathematical Functions](https://dlmf.nist.gov/24.4): the standard Bernoulli identities.
- The mathlib community, [mathlib](https://github.com/leanprover-community/mathlib4): the Bernoulli and Fourier mathematics used by the formal proof.
- Wenhua Zhao, [Generalizations of the image conjecture and the Mathieu conjecture](https://doi.org/10.1016/j.jpaa.2009.10.007): the introduction of Mathieu subspaces.
- Wenhua Zhao, [Mathieu subspaces of associative algebras](https://doi.org/10.1016/j.jalgebra.2011.09.036): their associative-algebra definition.
- Arno van den Essen, [An introduction to Mathieu subspaces](https://arxiv.org/abs/1907.06107v1): the Mathieu–Zhao terminology.
- Wenhua Zhao, [The LNED and LFED conjectures for algebraic algebras](https://doi.org/10.1016/j.laa.2017.08.016): positive cases discussed in the paper.
- Arno van den Essen and Wenhua Zhao, [On images of locally finite derivations and E-derivations](https://doi.org/10.1016/j.jpaa.2018.07.002): further positive cases discussed in the paper.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamLnedCounterexample2026,
  author       = {Graham, P.},
  title        = {{A counterexample to the E-derivation part of the LNED conjecture}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/lned-counterexample-v1/results/lned-counterexample}},
  doi          = {10.5281/zenodo.23735733}
}
```
