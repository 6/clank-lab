# The second-order asymptotic of the EKG sequence

[![Checks](https://github.com/6/clank-lab/actions/workflows/ekg-sequence.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/ekg-sequence.yml)

The [EKG sequence](https://mathworld.wolfram.com/EKGSequence.html)
([OEIS A064413](https://oeis.org/A064413)) starts with 1 and 2, then
repeatedly takes the smallest unused positive integer sharing a factor with
the previous term. Its graph looks like an electrocardiogram, hence the name.
In 2002 Lagarias, Rains and Sloane (LRS) conjectured its second-order growth.
In 2026 Tomer Haver
([*Explicit rates for the EKG sequence*](https://doi.org/10.5281/zenodo.23129632))
reduced the question to counting certain odd values in the sequence and
proved the upper half of the bound. This work proves the lower half and
extends it to every index, which completes the proof of the conjecture as
LRS displayed it, for almost all n as stated in their abstract, and in
fact gives the second-order asymptotic for every term on each of the three
branches (the paper's corollary “The three branches”). Replacing each
value p or 3p, for an odd prime p, by 2p gives the smoothed sequence b(n),
which satisfies

```text
b(n) = n + n/(3 log n) + o(n/log n).
```

Hofman and Pilipczuk proved the ratio form (LRS Conjecture 2).
LRS Conjecture 3, concerning global bounds, remains open.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Install [elan](https://github.com/leanprover/elan#installation), then run:

```sh
cd lean
lake exe cache get
lake build
```

A passing build checks the exact theorem statement, the finite sequence and
smoothing controls, and that all seven audited theorems use only Lean's
standard logical axioms. [lean/README.md](lean/README.md) gives the details.
The [numerical illustration](data/README.md) is optional and is not part of
the proof.

## Credits

This completes Tomer Haver's
[*Explicit rates for the EKG sequence*](https://doi.org/10.5281/zenodo.23129632)
(version 3, October 2026). Haver's estimates and the reduction to a counting
problem are used here as proved Lean theorems, and Haver had already proved
the upper half of the second-order bound. The conjecture is due to
[Lagarias, Rains and Sloane (2002)](https://doi.org/10.1080/10586458.2002.10504486),
and [Hofman and Pilipczuk (2008)](https://cs.uwaterloo.ca/journals/JIS/VOL11/Hofman/hofman1.html)
proved the ratio form (LRS Conjecture 2). The prime number theorem in Lean comes from
the [PrimeNumberTheoremAnd project](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
(A. Kontorovich, T. Tao et al.).

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamEkgSequence2026,
  author       = {Graham, P.},
  title        = {{The second-order asymptotic of the EKG sequence}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/ekg-sequence-v1/results/ekg-sequence}}
}
```
