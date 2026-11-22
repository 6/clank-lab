# Symmetric chains in noncrossing partition lattices

[![Checks](https://github.com/6/clank-lab/actions/workflows/noncrossing-symmetric-chains.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/noncrossing-symmetric-chains.yml)

A [noncrossing partition lattice](https://en.wikipedia.org/wiki/Noncrossing_partition) organizes factorizations of a Coxeter element in a [complex reflection group](https://en.wikipedia.org/wiki/Complex_reflection_group). A symmetric chain decomposition partitions it into chains that move one rank at a time and start and end equally far from the bottom and top. Henri Mühle asked in [2015](https://arxiv.org/abs/1509.06942v1) whether these lattices always have such a decomposition. Simion and Ullman, Reiner, Bessis and Corran, and Mühle established the infinite families and most exceptional cases. This work supplies the remaining exceptional cases and proves the chain assertion for every finite well-generated complex reflection group and every Coxeter element, including products. It does not settle Mühle's stronger Boolean-decomposition question.

<img src="data/scd-example.svg" width="830" alt="A rectangle of two chains partitioned into symmetric saturated chains, with equal endpoint-rank sums.">

Computer-assisted; not yet reviewed by experts.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23639462](https://doi.org/10.5281/zenodo.23639462)

## Abstract

Every noncrossing partition lattice of a finite well-generated complex reflection group admits a symmetric chain decomposition: a partition into saturated chains whose bottom and top ranks sum to the rank of the lattice. This answers the chain part of a question of Henri Mühle, who proved symmetric Boolean decompositions for the groups $G(d,d,n)$, symmetric chain decompositions for the exceptional types of rank at most four other than $H_4$, and the strong Sperner property for every well-generated group. With the theorems of Simion and Ullman for the symmetric groups and of Reiner for type $B$, and the isomorphism of Bessis and Corran between the lattices of $G(d,1,n)$ and of type $B$, six exceptional types remained: $H_4$, $G_{33}$, $G_{34}$, $E_6$, $E_7$ and $E_8$. For these, computer-found chains are checked exactly, and a finite criterion proves that each checked graph is the whole interval. Reflection automorphisms of Reiner, Ripoll and Stump carry the chains to every Coxeter element; a product construction treats reducible groups. Lean checks the abstract walk criterion, the product construction and the transfer along order isomorphisms, but not the group computations or the cited results.

This work has not yet been reviewed by experts. The proofs, the Lean formalization, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

## Check it

Use Python 3, Node.js, GAP with its SmallGrp library, and Lean through [elan](https://github.com/leanprover/elan). On Debian or Ubuntu, install the native requirements with `sudo apt-get install python3 nodejs gap-core gap-libs gap-smallgrp`. From this folder:

```sh
python3 checks/verify.py
cd lean
lake build
```

The first command reconstructs the six remaining intervals, checks their complete vertex and cover sets, checks every chain certificate with separately written Python and JavaScript programs sharing the chain files and GAP-generated interval graphs, and requires altered certificates to fail. The Lake build checks the abstract interval, product, transfer, and exceptional-reduction lemmas. It uses Lean's standard library, so there is no Mathlib cache to fetch. The endpoint statement is included; the classification and the published decomposition theorems are inputs to the paper's written reduction, rather than theorems proved in Lean. See the [checker guide](checks/README.md) and [Lean guide](lean/README.md) for the verification details; the [checking notes](checks/presentation-notes.md) include the formal dependencies.

## Credits

Henri Mühle posed the question, proved the $G(d,d,n)$ result and the small exceptional cases, and established the strong Sperner property in general. Rodica Simion and Daniel Ullman supplied the type-A decomposition; Victor Reiner supplied the type-B chains; David Bessis and Ruth Corran identified the other $G(d,1,n)$ lattices with type B. Patricia Hersh strengthened the type-B result to a Boolean decomposition. Christos A. Athanasiadis and Victor Reiner attribute a type-D symmetric chain decomposition to Eleni Tzanaki, citing a private communication ([author manuscript, Section 7, item 4](https://www-users.cse.umn.edu/~reiner/Papers/ncd.pdf)); Mühle also credits Tzanaki. Drew Armstrong asked whether generalized noncrossing partitions are strongly Sperner for every positive integer $k$ ([Open Problem 3.5.12](https://arxiv.org/abs/math/0611106v2)); Mühle had already proved the strong Sperner property for $k=1$, and this work supplies symmetric chain decompositions for the six remaining exceptional types at $k=1$ only. Reiner, Vivien Ripoll and Christian Stump proved the reflection-automorphism result used to cover every Coxeter element. Geoffrey Shephard and John Todd classified the groups. Drew Armstrong describes the real reflection models; Bessis records the invariant degrees. John Conway and Neil Sloane's construction, as developed by Manabu Oura and Jiro Sekiguchi, supplies the complex exceptional models. The paper discusses related work and gives the exact source statements used. Griggs's matching construction, in Tomon's iterative form, guided the chain search. The product construction goes back to de Bruijn, van Ebbenhorst Tengbergen and Kruyswijk; Srinivasan gives a modern account. Verification uses GAP, its SmallGrp library, Python, Node.js, and Lean.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamNoncrossingSymmetricChains2026,
  author       = {Graham, Peter},
  title        = {{Symmetric chains in noncrossing partition lattices}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/noncrossing-symmetric-chains-v3/results/noncrossing-symmetric-chains}},
  doi          = {10.5281/zenodo.23639462}
}
```
