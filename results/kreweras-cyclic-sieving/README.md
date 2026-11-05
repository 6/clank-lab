# Cyclic sieving for q-Kreweras numbers in the exceptional types

[![Checks](https://github.com/6/clank-lab/actions/workflows/kreweras-cyclic-sieving.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/kreweras-cyclic-sieving.yml)

The [noncrossing partitions](https://en.wikipedia.org/wiki/Noncrossing_partition) of a [Weyl group](https://en.wikipedia.org/wiki/Weyl_group) generalize the noncrossing set partitions counted by the [Catalan numbers](https://en.wikipedia.org/wiki/Catalan_number), and the chains of them of each length carry a natural cyclic action. A [cyclic sieving](https://en.wikipedia.org/wiki/Cyclic_sieving) polynomial is one whose values at the [roots of unity](https://en.wikipedia.org/wiki/Root_of_unity) count the chains fixed by each power of that action. In 2016 Victor Reiner and Eric Sommers defined a q-Kreweras number for each [nilpotent orbit](https://en.wikipedia.org/wiki/Nilpotent_orbit) of the Lie algebra, and conjectured that these polynomials sieve the chains sorted by the orbit of the space their bottom element fixes ([Conjecture 1.4](https://arxiv.org/abs/1605.09172v2)). They proved it for the classical types A, B, C and D. We prove it for the exceptional Weyl groups G2, F4, E6, E7 and E8, so the conjecture holds for every irreducible Weyl group. At $q=1$ the count was already a theorem of Theo Douvropoulos and Matthieu Josuat-Vergès ([Theorem 3.10](https://arxiv.org/abs/2209.12540v2)); what is new is every other root of unity. The proof follows Christian Krattenthaler and Thomas W. Müller's [reduction](https://arxiv.org/abs/1001.0028) of the unrefined cyclic sieving to finitely many cases: for fixed parameters both sides become polynomials of bounded degree in the chain length, so finitely many identities settle every length.

Computer-assisted; not yet reviewed by experts.

The proofs, the Lean formalization, the computer checks and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

The finite identities are checked by two independent exact programs, which rebuild each root system, its noncrossing partitions and the fixed-point polynomials from scratch, compare them with the certificates in `data/`, and evaluate the tabulated q-Kreweras numbers at roots of unity. With Python 3.12 or later, from this folder:

```sh
python3 -m pip install -r checks/requirements.txt
sh checks/check.sh
```

It takes about four minutes on one core, with under 1 GB of memory, and ends with `PASS: 12 of 12 checks`. `sh checks/check.sh --part K/N` runs every N-th check. The [checker documentation](checks/README.md) describes each program and the certificate format.

The reduction of the conjecture to these identities is checked in Lean. Install Lean using [elan](https://github.com/leanprover/elan); a network connection is needed for the dependencies and their compiled cache. Allow a few minutes for the download and about two minutes for the build, with about 8 GB of memory.

```sh
cd lean
lake exe cache get
lake build
```

The build checks the reduction from the facts the programs verify and the axioms it uses. [Lean details](lean/README.md) give the formal statement, how each hypothesis is checked, and what stays outside Lean.

## Credits

Victor Reiner and Eric Sommers posed the conjecture in *Weyl group q-Kreweras numbers and cyclic sieving* (Annals of Combinatorics, 2018), proved it in types A, B, C and D, and tabulated the q-Kreweras numbers of the exceptional types that this proof evaluates. Theo Douvropoulos and Matthieu Josuat-Vergès proved the refined count at $q=1$ in *The generalized cluster complex: refined enumeration of faces and related parking spaces* (SIGMA, 2023), completing work of Brendon Rhoades. The reduction to finitely many cases follows Christian Krattenthaler and Thomas W. Müller's proof of the unrefined cyclic sieving in the exceptional types, and the cyclic action is Drew Armstrong's, in David Bessis and Victor Reiner's form.

Lucas Pouillart, for faces of the cluster complex, and Christian Krattenthaler and Christian Stump, for positive noncrossing partitions, study nearby refinements of these cyclic sieving phenomena, which this result does not address. The reduction is formalized with Lean 4 and Mathlib, and the checkers use python-flint and NumPy. [Further credits](checks/README.md#further-credits) give the exact references.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamKrewerasCyclicSieving2026,
  author = {Graham, P.},
  title = {{Cyclic sieving for q-Kreweras numbers in the exceptional types}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/kreweras-cyclic-sieving-v1/results/kreweras-cyclic-sieving}}
}
```
