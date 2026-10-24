# A monotone counterexample to a question on distributional complexity

[![Checks](https://github.com/6/clank-lab/actions/workflows/monotone-query-gap.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/monotone-query-gap.yml)

A [Boolean function](https://en.wikipedia.org/wiki/Boolean_function) takes
bits as inputs and returns a bit. An adaptive algorithm queries inputs
until the output is determined; a subcube partition describes each input
by a unique partial assignment that determines the output. Laurin
Köhler-Schindler and Jeffrey E. Steif asked in
[Question 2.1 of their paper](https://arxiv.org/abs/2408.12995v1), first posted
on August 23, 2024 and [published in ACM Transactions on Computation Theory](https://doi.org/10.1145/3814613)
on May 19, 2026, whether the best average costs of these descriptions
agree for every monotone function when the inputs are independent coins
with a common bias. Monotone means that changing an input from 0 to 1
cannot change the output from 1 to 0.
Their nonmonotone ALL-EQUAL example on three inputs and four-input function
$h$ already give strict gaps (arXiv v1, Example 2.4 and Section 2.3).
The explicit monotone function below answers their question in the negative
for fair coins, with algorithmic cost $13/4$ and partition cost $51/16$:

$$
f(x_0,x_1,x_2,x_3,x_4)=x_1x_2x_3\lor x_0x_4(x_1\lor x_2\lor x_3).
$$

Here products mean AND and $\lor$ means OR. Lean checks the strict gap;
two independent exact certificate checkers also establish that the stated
partition cost is optimal.

Computer-assisted; not yet reviewed by experts.

The proofs, the Lean formalization, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23578348](https://doi.org/10.5281/zenodo.23578348)

## Check it

Requirements: Python 3.10 or later, [elan](https://github.com/leanprover/elan)
for Lean, Git, and an internet connection for the first dependency download.
The Python checks use only the standard library. From this folder:

```sh
python3 -I checks/check.py
cd lean
lake exe cache get
lake build
```

Allow a few minutes with the dependency cache. The [Lean project notes](lean/README.md)
and [certificate notes](checks/README.md) describe the precise statements
and checks.

## Credits

Laurin Köhler-Schindler and Jeffrey E. Steif posed the question, developed
the distributional comparison framework used here, and supplied the
nonmonotone strict-gap examples that precede this result. Their paper,
[*A study of distributional complexity measures for Boolean functions*](https://doi.org/10.1145/3814613),
appeared in ACM Transactions on Computation Theory, online May 19, 2026,
after acceptance on April 4, 2026; it was first posted August 23, 2024 as
[arXiv:2408.12995](https://arxiv.org/abs/2408.12995v1).
We use their definitions and notation. The question's wording and numbering,
and the example numbers, are cited from arXiv v1,
the only arXiv version listed. The [open author manuscript](https://www.math.chalmers.se/~steif/p74.pdf)
retains Question 2.1 unchanged; ACM's final typeset text was not accessible
to us. Our own Python enumeration code, using
[Google OR-Tools' CP-SAT solver](https://developers.google.com/optimization/cp/cp_solver),
found the example. That search code is not part of this proof bundle.

Robin Kothari, David Racicot-Desloges and Miklos Santha proved earlier separations for worst-input decision-tree and
subcube partition costs in
[their 2015 paper](https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2015.915).
Srinivasan Arunachalam, Sourav Chakraborty, Michal Koucký, Nitin Saurabh and
Ronald de Wolf studied the same uniform partition cost as average
unambiguous certificate complexity in
[their work on Fourier entropy](https://arxiv.org/abs/1809.09819).
Lean and its library contributors provide the proof-checking infrastructure.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamMonotoneQueryGap2026,
  author       = {Graham, P.},
  title        = {{A monotone counterexample to a question on distributional complexity}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/monotone-query-gap-v2/results/monotone-query-gap}},
  doi          = {10.5281/zenodo.23578348}
}
```
