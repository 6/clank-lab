# Smith normal form of the n-cycle class sum

[![Checks](https://github.com/6/clank-lab/actions/workflows/stanley-class-sum-snf.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/stanley-class-sum-snf.yml)

A permutation rearranges $n$ objects; permutations with the same cycle lengths form a conjugacy class. Adding the permutations in each class gives a basis for the center of the integral [group ring](https://en.wikipedia.org/wiki/Group_ring) of the [symmetric group](https://en.wikipedia.org/wiki/Symmetric_group). Multiplication by the sum of all $n$-cycles is therefore an integer matrix. Its [Smith normal form](https://en.wikipedia.org/wiki/Smith_normal_form) describes the quotient of all integer combinations of class sums by the multiples of the $n$-cycle class sum. In [2019, Richard P. Stanley](https://mathoverflow.net/questions/335226) conjectured its nonzero diagonal entries when $n$ is an odd prime or twice an odd prime, and suggested that more data might lead to a conjecture for all $n$. We prove that, for every $n\geq1$, there are $p(n)-n$ zero entries, where $p(n)$ counts partitions of $n$, and the nonzero entries are

```math
d_0=1,\qquad d_r=\frac{a_r r!}{\gcd(n,r)},\qquad
a_r=\begin{cases}2,&r\equiv n\pmod 2,\\1,&r\not\equiv n\pmod 2,\end{cases}
\qquad 1\leq r<n.
```

This confirms both conjectures and establishes a formula for every positive $n$. The proof builds on classical character theory of the symmetric group and determines the integral lattices needed to pass from character values to Smith normal form; [Stanley's survey](https://arxiv.org/abs/1602.00166v2) gives the broader combinatorial context. Lean checks the image-lattice theorem and the divisor chain directly from permutation and group-ring definitions, including the character formula used in the proof. The equivalent diagonal form and the two prime cases are derived in the written proof.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23591100](https://doi.org/10.5281/zenodo.23591100)


## Check it

Install [elan](https://github.com/leanprover/elan), the standard Lean toolchain manager, and Git. From this folder, run:

```sh
cd lean
lake exe cache get
lake build
```

The build checks the proof, the final statement, and its permitted logical dependencies. No separate computation or certificate checker is needed. The [Lean guide](lean/README.md) explains the formal statement and its correspondence with the paper; [checking notes](lean/checking-notes.tex) retain the detailed declarations and logical dependencies.

## Credits

Richard P. Stanley posed the question and the two conjectures and supplied the motivating examples, inspired by [Nathan Lindzey's Cayley-graph question](https://mathoverflow.net/questions/334899). Frobenius's class-multiplication formula and the classical hook characters provide the representation-theoretic starting point. Alain Goupil and Gilles Schaeffer's [work on long-cycle factorizations](https://doi.org/10.1006/eujc.1998.0215), and [Philippe Biane's algebraic proof](https://www.mat.univie.ac.at/~slc/wpapers/s51biane.pdf), give the corresponding connection coefficients. Darij Grinberg's [introduction to the symmetric group algebra](https://arxiv.org/abs/2507.20706) supplies a contemporary exposition of class sums and representations. Tommy Wuxing Cai and Stanley's [work on Young's lattice](https://arxiv.org/abs/1502.00922) provides related context. The formal proof uses Lean and the mathlib library.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamStanleyClassSumSnf2026,
  author       = {Graham, P.},
  title        = {{Smith normal form of the n-cycle class sum}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/stanley-class-sum-snf-v4/results/stanley-class-sum-snf}},
  doi          = {10.5281/zenodo.23591100}
}
```
