# A counterexample on two kinds of positive dependence

[![Checks](https://github.com/6/clank-lab/actions/workflows/ft23-pqd-pmi.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/ft23-pqd-pmi.yml)

A [copula](https://en.wikipedia.org/wiki/Copula_(statistics)) describes how two random quantities depend on each other, separately from their individual distributions. Sebastian Fuchs and Marco Tschimpke conjectured in 2023 that two ways of expressing positive dependence coincide for Archimedean copulas. Building on their definition of positive measure inducing dependence (PMI), we give an explicit Archimedean copula that is positively quadrant dependent (PQD) but is not PMI. The converse implication and their separate conjecture about negative dependence remain unresolved here.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Install [elan](https://github.com/leanprover/elan) and Git. From this folder, download the dependencies and check the proof:

```sh
cd lean
lake exe cache get
lake build
```

Allow several minutes for dependency downloads and a few minutes for the proof. The build checks the full theorem, its statement, the independence example and its permitted axioms. [Formalization details](lean/README.md) explain the definitions and requirements.

## Credits

Sebastian Fuchs and Marco Tschimpke introduced PMI and posed the equivalence answered here in Conjecture 1 of [their paper](https://doi.org/10.1016/j.jmva.2023.105259). Their Definition 1 and reflected-copula construction determine the precise condition we disprove. Their Example 6 establishes the equivalence for the Frank family; this counterexample concerns the larger Archimedean class. The paper's definitions and its distinction between measure positivity and a density criterion are essential to the argument.

The proof uses the classical convex-generator description of bivariate Archimedean copulas, developed in the broader dimensional setting by [Alexander McNeil and Johanna Nešlehová](https://doi.org/10.1214/07-AOS556). The particular generator, the global PQD inequality and the negative rectangle are proved directly. The formalization uses [Lean](https://lean-lang.org/) and the [mathlib community's library](https://github.com/leanprover-community/mathlib4) for real analysis, convexity, measures and exact arithmetic. These tools check the measure-theoretic statement without assuming that the copula has a density. [Further credits](checks/README.md) identify the superadditivity criterion and work on singular level curves that informed the construction.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamFt23PqdPmi2026,
  author = {Graham, P.},
  title = {{A counterexample on two kinds of positive dependence}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/ft23-pqd-pmi-v1/results/ft23-pqd-pmi}}
}
```
