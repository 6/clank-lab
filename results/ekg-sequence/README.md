# The second-order asymptotic of the EKG sequence

[![Checks](https://github.com/6/clank-lab/actions/workflows/ekg-sequence.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/ekg-sequence.yml)

The [EKG sequence](https://mathworld.wolfram.com/EKGSequence.html)
([OEIS A064413](https://oeis.org/A064413)), discovered by Jonathan Ayres,
starts with 1 and 2, then
repeatedly takes the smallest unused positive integer that shares a factor
with the previous term. Its graph looks like an electrocardiogram, hence the
name.

In 2002 Lagarias, Rains and Sloane conjectured its second-order growth:
$a(n) = n + \frac{n}{3\log n} + o\bigl(\frac{n}{\log n}\bigr)$ for almost all $n$. Replacing each value
$p$ or $3p$, for an odd prime $p$, by $2p$ smooths out the sequence's spikes and
gives $b(n)$. We prove the asymptotic along the full sequence of indices as
$n \to \infty$:

$$b(n) = n + \frac{n}{3\log n} + o\Bigl(\frac{n}{\log n}\Bigr).$$

The statement is eventual: for each $\varepsilon > 0$ the error is at most
$\varepsilon n/\log n$ for all $n$ beyond some $N(\varepsilon)$. Since
$a(n) = b(n)$ except at the indices where $a(n)$ is an odd prime or three
times one, a set of density zero, the formula holds for $a(n)$ at almost
all $n$. This proves the additive second-order interpretation in their PDF abstract.
Their numbered Conjecture 2, read literally, asks only for ratio limits,
which Hofman and Pilipczuk already proved.

This builds directly on Tomer Haver's
[*Explicit rates for the EKG sequence*](https://doi.org/10.5281/zenodo.23129632)
(2026), which reduced the question to counting certain odd values and
proved the upper half of the bound in the manuscript. We prove the lower
half and pass from Haver's frontier times to the full sequence of indices.
Lagarias, Rains and Sloane's Conjecture 3, on global bounds, is proved in
the companion [sharp EKG bounds paper](../ekg-bounds/README.md).

As consequences we settle two sets of OEIS conjectures. Ordowski
conjectured in 2009 that $a(n) > n$ almost everywhere when $a(n)$ is not
prime, and that the proportion of $k \le N$ with $a(k) > k$ tends to 1. We
prove both, the first in a stronger form: for all large $n$, $a(n) > n$
exactly when $a(n)$ is composite. Jasinski conjectured in 2008 that
[A152458](https://oeis.org/A152458) ($a(n) = n$) is finite and that the
three lines $a(n) = n$, $2a(n) = n$ and $2a(n) = 3n$ carry only finitely
many points ([A152519](https://oeis.org/A152519)); we prove both.
These consequences are checked in Lean too. The paper also derives the
three separate branch formulas by a short algebraic argument; those
corollary statements are not separately formalized in Lean.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23572881](https://doi.org/10.5281/zenodo.23572881)

## Check it

Install [elan](https://github.com/leanprover/elan#installation), then run:

```sh
cd lean
lake exe cache get
lake build
```

A passing build checks the exact statements of the theorem and its
consequences, the finite sequence and smoothing controls, and that all
fourteen audited theorems use only Lean's standard logical axioms.
[lean/README.md](lean/README.md) gives the details.
The [numerical illustration](data/README.md) is optional and is not part of
the proof.

## Credits

Jonathan Ayres discovered the sequence and observed its three lines, as
credited by [Lagarias, Rains and Sloane](https://arxiv.org/abs/math/0204011).
This completes Tomer Haver's
[*Explicit rates for the EKG sequence*](https://doi.org/10.5281/zenodo.23129632)
(version 3, October 2026). From Haver's Lean sources we import, as proved
theorems, the sequence's construction and permutation property, the prime
pattern $2p, p, 3p$, the bounds on early even values, on the span of used
values and on missing composites, and the rate $b(n) = n + O(n/\log n)$.
Haver's manuscript also reduces the question to a counting problem
(Corollary 2(e)) and proves the upper half of the second-order bound
(abstract and Theorem 1(d)); these are outside his Lean coverage, and our
Lean proof derives the counting identity and the sharp coefficient itself. The conjecture is due to
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
  howpublished = {\url{https://github.com/6/clank-lab/tree/ekg-sequence-v4/results/ekg-sequence}},
  doi          = {10.5281/zenodo.23572881}
}
```
