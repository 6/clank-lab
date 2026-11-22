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

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23638220](https://doi.org/10.5281/zenodo.23638220)

## Abstract

We determine the Smith normal form of multiplication by the sum of all $n$-cycles on the center of $\mathbb{Z} S_n$. For every $n\geq1$, it has $p(n)-n$ zero entries, where $p(n)$ counts partitions of $n$, and nonzero factors $d_0=1$ and $d_r=a_r r!/\gcd(n,r)$ for $1\le r<n$, with $a_r=2$ when $r\equiv n\pmod2$ and $a_r=1$ otherwise. In 2019 Stanley conjectured these factors when $n$ is an odd prime or twice an odd prime; the formula proves both conjectures and covers every $n$. Goupil and Schaeffer gave a character-sum formula for the long-cycle connection coefficients and turned it into a positive-term formula. Biane reproduced the character-sum formula and gave a short algebraic proof of their positive-term formula. Following Biane, we derive the character-sum formula from Frobenius's formula; Grinberg's exposition supplies class-sum and representation-theory background. Through hook characters, the character-sum formula writes the matrix as a product of three matrices. We add the integral structure: we determine the lattices spanned by the two outer factors and show that, in a suitable basis, row $r$ of the remaining product is divisible by $d_r$. The image lattice and the divisibility $d_r\mid d_{r+1}$ are checked in Lean from the group-ring definitions, including the character formula. The diagonal form and the prime cases follow by written arguments.

This work has not yet been reviewed by experts. The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

## Check it

Install [elan](https://github.com/leanprover/elan), the standard Lean toolchain manager, and Git. From this folder, run:

```sh
cd lean
lake exe cache get
lake build
```

The build checks the proof, the final statement, and its permitted logical dependencies. No separate computation or certificate checker is needed. The [Lean guide](lean/README.md) explains the formal statement and its correspondence with the paper; [checking notes](lean/checking-notes.tex) retain the detailed declarations and logical dependencies.

## Credits

Richard P. Stanley's [Smith normal form of conjugacy class actions](https://mathoverflow.net/questions/335226) poses the question and two conjectures, with motivating examples. Bruce E. Sagan's [The Symmetric Group: Representations, Combinatorial Algorithms, and Symmetric Functions](https://doi.org/10.1007/978-1-4757-6804-6) presents Frobenius's class-multiplication formula and the classical hook characters used as the starting point of the proof.

Alain Goupil and Gilles Schaeffer's [Factoring n-cycles and counting maps of given genus](https://doi.org/10.1006/eujc.1998.0215) gives the long-cycle connection coefficients. Philippe Biane's [Nombre de factorisations d’un grand cycle](https://www.mat.univie.ac.at/~slc/wpapers/s51biane.pdf) reproduces the character-sum formula and proves the positive-term form. The Lean contributors' [Lean 4](https://github.com/leanprover/lean4) and the mathlib contributors' [mathlib](https://github.com/leanprover-community/mathlib4) supply the proof assistant and formal-proof library used to check the image-lattice theorem and divisor chain.

Further credits and source notes are in [the checking documentation](checks/README.md).

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamStanleyClassSumSnf2026,
  author       = {Graham, Peter},
  title        = {{Smith normal form of the n-cycle class sum}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/stanley-class-sum-snf-v5/results/stanley-class-sum-snf}},
  doi          = {10.5281/zenodo.23638220}
}
```
