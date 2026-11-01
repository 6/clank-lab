# The queueing polynomial is convex

[![Checks](https://github.com/6/clank-lab/actions/workflows/queueing-polynomial-convexity.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/queueing-polynomial-convexity.yml)

In a [queueing system](https://en.wikipedia.org/wiki/Queueing_theory), sending copies of a job to several servers can reduce waiting. A polynomial describes how the probabilities of choosing groups of servers affect job occupancy. [Brosch, Laurent and Steenkamp](https://doi.org/10.1137/20M1369592) conjectured in 2020 that this polynomial is [convex](https://en.wikipedia.org/wiki/Convex_function): mixing two assignment rules never gives a value above the corresponding average. We prove their Conjecture 1 for every number of servers $n$, group size $L$, and degree $d$ with $n,L,d\ge2$. The proof uses classical complete homogeneous symmetric polynomials and a finite vertex-deletion identity.

More generally, the polynomial is convex on the whole nonnegative orthant for every $n,d\ge0$ and $L\ge1$, before imposing that the assignment probabilities sum to one. This includes the empty edge set when $L>n$; its probability simplex is empty.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Install [Lean through elan](https://github.com/leanprover/elan), Git, and an internet connection for the dependencies. From this folder:

```sh
cd lean
lake exe cache get
lake build
```

The first download can take several minutes and needs several gigabytes of disk space. With the dependency cache available, the proof and examples take about a minute on a recent machine. The build checks the original polynomial, both theorem statements, small examples, and the proof's permitted axioms. [The Lean guide](lean/README.md) describes the modules and checks.

## Credits

[Daniel Brosch, Monique Laurent and Andries Steenkamp](https://doi.org/10.1137/20M1369592) posed the conjecture and proved early cases. [Sven Polak](https://doi.org/10.1137/21M1413298) extended the edge-size-two case through degree nine. The coefficients come from product-form queueing models surveyed by [Kristen Gardner and Rhonda Righter](https://arxiv.org/abs/2006.05979v1). The representation specializes [Albert Marshall and Ingram Olkin's classical exponential construction](https://purl.stanford.edu/kb905zm7154); convexity of complete homogeneous polynomials follows from [John McLeod's 1959 inequality](https://doi.org/10.1017/S0013091500021921). These ingredients are prior work. Here they give a finite proof of the full queueing conjecture.

The work uses the [Lean proof assistant](https://lean-lang.org/) and the [Mathlib library](https://github.com/leanprover-community/mathlib4). These tools check the formal definitions and deductions, including the source polynomial's ordered tuples and repeated edges, the deletion recurrence, the complete homogeneous convexity argument, and the final simplex and orthant statements. The paper explains the correspondence between those statements and the published question.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamQueueingPolynomialConvexity2026,
  author = {Graham, P.},
  title = {{The queueing polynomial is convex}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/queueing-polynomial-convexity-v1/results/queueing-polynomial-convexity}}
}
```
