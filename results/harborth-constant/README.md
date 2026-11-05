# The Harborth constant of Cp ⊕ Cp for every prime p ≥ 11

[![Checks](https://github.com/6/clank-lab/actions/workflows/harborth-constant.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/harborth-constant.yml)

The [Erdős–Ginzburg–Ziv theorem](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Ginzburg%E2%80%93Ziv_theorem) began the study of [zero-sum problems](https://en.wikipedia.org/wiki/Zero-sum_problem): how many elements of a finite abelian group force some of them to add up to zero. The Harborth constant of a group is the least $k$ such that every set of $k$ distinct elements contains as many distinct elements as the group's exponent whose sum is zero. For the grid $C_p\oplus C_p$ of pairs of residues modulo a prime $p$, that means $p$ distinct points summing to zero. Gao and Thangadurai conjectured in 2004 that the answer for $C_n\oplus C_n$ with $n$ odd is $2n-1$ and proved it for primes $p\ge 67$. Gao, Geroldinger and Schmid extended this to $p\ge 47$ in 2007, and Kemnitz had settled $p = 3, 5, 7$ in 1983. Béla Bajnok's book of open problems in additive combinatorics asks for the remaining primes $11\le p\le 43$ (Problem F.100). We prove that the Harborth constant of $C_p\oplus C_p$ is $2p-1$ for every prime $p\ge 11$, which answers that problem. The proof extends the method of Gao, Thangadurai, Geroldinger and Schmid.

With Kemnitz's values, the conjecture holds for every odd prime. The composite case stays open.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Install Lean using [elan](https://github.com/leanprover/elan). A network connection is needed to download Mathlib and its compiled cache, about 5 GB. Allow a few minutes for the download and about three minutes for the build, with about 9 GB of memory.

```sh
cd lean
lake exe cache get
lake build
```

The build checks the theorem for every prime $p\ge 11$, the lower bound for every odd prime, the value of the constant, small examples of the definition and the axioms used. [Lean details](lean/README.md) give the dependency pins and how the formal statements match the paper. A separate program, which needs only Python 3 and runs in under a second, checks the finite step for $p = 11$ and $13$ independently of Lean:

```sh
python3 checks/shape_check.py
```

## Credits

Weidong Gao and Ravindranathan Thangadurai posed the conjecture in *A variant of Kemnitz conjecture* (Journal of Combinatorial Theory, Series A, 2004), proved it for primes at least 67, and gave the lifting lemma and the averaging over directions that this proof starts from. Weidong Gao, Alfred Geroldinger and Wolfgang Schmid, in *Inverse zero-sum problems* (Acta Arithmetica, 2007), proved it for primes at least 47 with the layer method this proof extends, and Gao, Qing-Hu Hou, Schmid and Thangadurai, in *On short zero-sum subsequences II* (Integers, 2007), extended the lifting criterion to higher rank. Béla Bajnok recorded the remaining primes as Problem F.100 of *Additive Combinatorics: A Menu of Research Problems*, and Arnfried Kemnitz proved the lower bound and settled the primes up to 7.

What is new here is a criterion that applies the theorem of Dias da Silva and Hamidoune to every layer of the projected multiset at once, and the analysis of the resulting fiber-size patterns down to $p = 11$. The proof also uses the Cauchy–Davenport theorem. It is formalized with Lean 4 and Mathlib. [Further credits](checks/README.md) give the exact references.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamHarborthConstant2026,
  author = {Graham, P.},
  title = {{The Harborth constant of Cp ⊕ Cp for every prime p ≥ 11}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/harborth-constant-v1/results/harborth-constant}}
}
```
