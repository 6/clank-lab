# A counterexample to the very sparse greedy conjecture for random hitting sets

[![Checks](https://github.com/6/clank-lab/actions/workflows/random-hitting-set-greedy.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/random-hitting-set-greedy.yml)

In the [hitting set problem](https://en.wikipedia.org/wiki/Set_cover_problem) one chooses as few columns of a zero-one matrix as possible so that every row has a one in a chosen column. The [greedy algorithm](https://en.wikipedia.org/wiki/Greedy_algorithm) repeatedly takes the column covering the most uncovered rows; the [linear programming relaxation](https://en.wikipedia.org/wiki/Linear_programming_relaxation) gives a lower bound $L$. Arpino, Dmitriev and Grometto studied random $m\times n$ matrices with independent entries equal to one with probability $p$. They proved that greedy is within a constant factor of the optimum in a wide range, and in 2023 conjectured that the ratio of greedy to $L$ tends to one when $mp\to0$. We show that it does not: for $m=k$, $n=k^{10}$ and $p=1/(10k^4)$, greedy exceeds $L$ by a fixed factor with a fixed positive probability, for every $k\ge10^{20}$. This holds both when ties are broken by the leftmost column, as in their analysis, and when they are broken uniformly at random.

So the ratio does not converge to one in probability. Whether some other tie-breaking rule, or the best greedy run, achieves ratio tending to one remains open.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23915338](https://doi.org/10.5281/zenodo.23915338)

## Check it

Install [Lean through elan](https://github.com/leanprover/elan), Git, and an internet connection for the dependencies. From this folder:

```sh
cd lean
lake exe cache get
lake build
```

The first download takes several minutes and several gigabytes of disk space. With the dependency cache in place, the build takes a few minutes on a recent machine and needs about 6 GB of memory. It checks both theorems, their statements with the definitions unfolded, small example matrices, and that the main theorems use only Lean's standard axioms. [The Lean guide](lean/README.md) describes the modules.

## Credits

[Gabriel Arpino, Daniil Dmitriev and Nicolo Grometto](https://doi.org/10.4230/LIPIcs.APPROX/RANDOM.2024.30) posed the question, as Conjecture 12 of their paper ([first posted on arXiv](https://arxiv.org/abs/2305.05565v1)), and introduced the random model, the greedy and linear programming values compared here and the assumptions our parameters satisfy. Their theorems give the constant-factor agreement that this result shows cannot be sharpened to a ratio tending to one. The greedy algorithm for covering goes back to the analyses of [László Lovász](https://doi.org/10.1016/0012-365X(75)90058-8) and [David Johnson](https://doi.org/10.1016/S0022-0000(74)80044-9).

The proof is an elementary counting argument on isolated paths of three triples, with an exact exchange argument for uniform tie-breaking. It was formalized with the [Lean proof assistant](https://lean-lang.org/) and the [Mathlib library](https://github.com/leanprover-community/mathlib4), which check the random matrix law, both greedy rules, the linear programming value and the final probability statements from their definitions.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamRandomHittingSetGreedy2026,
  author = {Graham, P.},
  title = {{A counterexample to the very sparse greedy conjecture for random hitting sets}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/random-hitting-set-greedy-v1/results/random-hitting-set-greedy}},
  doi          = {10.5281/zenodo.23915338}
}
```
