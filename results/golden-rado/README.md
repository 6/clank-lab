# A conjecture of Hopkins on golden Rado numbers

[![Checks](https://github.com/6/clank-lab/actions/workflows/golden-rado.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/golden-rado.yml)

Color the integers $1, 2, \dots, N$ with two colors, 0 and 1, so that $1$ gets color 0 and no two consecutive integers both get color 1; such colorings are the words of the [golden mean shift](https://en.wikipedia.org/wiki/Subshift_of_finite_type) of symbolic dynamics. [Rado's theorem](https://en.wikipedia.org/wiki/Rado%27s_theorem_(Ramsey_theory)) concerns which equations have monochromatic solutions in every coloring. In 2021 Brian Hopkins defined the golden Rado number of $ax + by = z$, for $1 \le a \le b$, as the least $N$ such that every such coloring has a solution with $x$, $y$ and $z$ of one color, and conjectured that it equals $a^2(\ell+1)^2$ when $b = \ell a$. Hopkins proved the case $\ell = 1$ and found the values for $a = 1$, which show that the formula fails when $a = 1$ and $\ell \ge 2$. We prove the formula for every $a \ge 2$ and $\ell \ge 1$, which settles all the remaining cases of the conjecture. For example, for $2x + 4y = z$ the answer is 36. The result builds on Hopkins's definitions and known cases.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

With [elan](https://github.com/leanprover/elan) installed, run:

```sh
cd lean
lake exe cache get
lake build
```

The first command downloads Mathlib's compiled files (a few gigabytes); the build then takes a few minutes. It checks the proof, the exact statements and the axioms the main theorems use. The [checking notes](lean/README.md) give the formal statements and how they match the paper.

## Credits

Brian Hopkins introduced shift-constrained Rado numbers and posed this conjecture as Conjecture 1 of [Introducing shift-constrained Rado numbers](https://math.colgate.edu/~integers/graham16/graham16.pdf) (Integers 21A, 2021), supported by computations. The definitions used here are Hopkins's, and Hopkins's Theorems 1 and 2 settle the cases $a = 1$ and $\ell = 1$. Hopkins acknowledges Katrina Luckenbach and Matthew Vieira, who explored these topics as undergraduate research students. The unconstrained two-color Rado number of $ax + by = z$, conjectured by Hopkins and Schaal and proved by [Guo and Sun](https://doi.org/10.1016/j.jcta.2007.06.001), is the background for the question.

The proof is elementary: an explicit coloring by multiples of $a$ gives the lower bound, and a descent followed by a shift-invariance argument gives the upper bound. The formal proof uses the Lean 4 proof assistant and its Mathlib library.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamGoldenRado2026,
  author       = {Graham, P.},
  title        = {{A conjecture of Hopkins on golden Rado numbers}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/golden-rado-v1/results/golden-rado}}
}
```
