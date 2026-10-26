# Arbitrarily long avoidance of 3 in Euclid–Mullin sequences

[![Checks](https://github.com/6/clank-lab/actions/workflows/cameron-donkin.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/cameron-donkin.yml)

Starting with a prime, repeatedly take the smallest prime divisor of one plus the product of all preceding terms. This gives a [Euclid–Mullin sequence](https://en.wikipedia.org/wiki/Euclid%E2%80%93Mullin_sequence). Steve Donkin asked in [Cameron's Problem 19, first question](https://cameroncounts.github.io/web/QM/oldprob.html) whether, for every positive integer $n$, some prime seed has no 3 among its first $n$ terms, counting the seed. [Cameron's 2012 discussion](https://cameroncounts.wordpress.com/2012/10/05/a-prime-problem/) reports John Bray's computations. We prove the assertion by congruences and Dirichlet's theorem, extending Booker and Irvine's method for prescribing factor paths to enforce the smallest-factor rule. The separate question of one prime seed avoiding 3 forever remains open.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Install [elan](https://github.com/leanprover/elan), Git and the standard build tools. From `lean/`, run:

```sh
lake exe cache get
lake build
```

The build checks the proof, the exact statement, small sequence examples and the axiom restrictions. Checking the local proof takes about a minute once the dependencies are available; downloading them takes longer. The [checking notes](lean/README.md) give the definitions and proof structure.

## Credits

Steve Donkin posed the question, and Peter J. Cameron recorded it and reported John Bray's numerical work. Labos Elemer's [OEIS A093780](https://oeis.org/A093780), extended by David Wasserman, lists the least seeds whose first 3 occurs at positions 1 through 15. Andrew R. Booker and Sean A. Irvine's [The Euclid–Mullin graph](https://arxiv.org/abs/1508.03039v2), Lemma 2.2 and Remark 2.16, gives the related CRT factor-path method and prime starting values for loop constructions. The proof here adds simultaneous exclusion of all smaller prime factors. Marcello Paris's [related formalization](https://github.com/marcellop71/EM/tree/d04b90f5d132a452e29df91ee09ea903b811ad92) proves that suitable seed congruences preserve a fixed finite sequence of multipliers. Mathlib supplies formal proofs of the Chinese remainder theorem and Dirichlet's theorem.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamCameronDonkin2026,
  author       = {Graham, P.},
  title        = {{Arbitrarily long avoidance of 3 in Euclid--Mullin sequences}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/cameron-donkin-v1/results/cameron-donkin}}
}
```
