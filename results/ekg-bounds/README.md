# Sharp linear bounds for the EKG sequence

[![Checks](https://github.com/6/clank-lab/actions/workflows/ekg-bounds.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/ekg-bounds.yml)

The [EKG sequence](https://mathworld.wolfram.com/EKGSequence.html)
([OEIS A064413 entry](https://oeis.org/A064413)) starts with 1 and 2, then
repeatedly takes the smallest unused positive integer that shares a factor
greater than 1 with the previous term: 1, 2, 4, 6, 3, 9, 12, 8, 10, 5, 15, …
Most terms $a(n)$ are close to $n$. Each odd prime $p$ comes right after
$2p$ and right before $3p$; when $a(n) = p$, $p$ is about $n/2$, and the
next term $3p$ is about $3n/2$.

In 2002 Lagarias, Rains and Sloane conjectured that the smallest and
largest values of $a(n)/n$ occur at $n = 28$ and $n = 7$
([Conjecture 3](https://arxiv.org/abs/math/0204011), end of §4): for every
$n \ge 1$,

```math
\frac{13}{28}\,n \le a(n) \le \frac{12}{7}\,n,
```

with equality only at $a(28) = 13$ and $a(7) = 12$. We prove this.

![Left: a(n)/n for n up to 60, between the lines 12/7 and 13/28, touching them at n = 7 and n = 28. Right: the largest and smallest a(n)/n in each block from 2^k to 2^(k+1), for n up to one million, settling near 3/2 and 1/2.](data/ratio.svg)

Lagarias, Rains and Sloane proved $n/260 \le a(n) \le 14n$. Hofman and
Pilipczuk (2008) proved that $a(n)/n$ tends to $1/2$ when $a(n)$ is prime,
to $3/2$ when $a(n)$ is three times a prime, and to $1$ otherwise. Tomer
Haver's *Explicit rates for the EKG sequence* (2026) made these limits
explicit and checked them in Lean, and our earlier
[second-order asymptotic](https://doi.org/10.5281/zenodo.23493113) built on
Haver's work. These do not give the sharp constants at every $n$; using
their explicit estimates for this purpose requires enormous thresholds.
Haver already closes a self-improving early-even inequality and obtains
its leading asymptotic constant ([Lemma 4, Theorem 5 and Remark 6(b)](https://zenodo.org/records/23129632/files/EKG-rates-paper.pdf)). We shorten its prime window from $4K+3$
to $3K+2$ integers and combine effective large-sieve constants with odd-term
control.
It makes the explicit estimates work once that smallest unused even number
passes about $1.3 \times 10^{10}$, which happens within the first
$1.6 \times 10^{10}$ terms; those terms are computed.

The deduction is a Lean proof from the definition of the sequence,
conditional on computed premises. It uses
Haver's Lean estimates, and explicit prime-counting bounds and large-sieve
inequalities that are also proved in Lean. Its only premises are four
computed facts: three about the first $1.6 \times 10^{10}$ terms, each
computed by two independent programs that agree, and an interval-arithmetic
certificate for the middle range, checked by a separate program written
from the Lean statement. That the programs compute the quantities named in
the Lean premises was checked by reading the code, not by machine.

Computer-assisted; not yet reviewed by experts.

The proofs, the Lean formalization, the programs and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23732014](https://doi.org/10.5281/zenodo.23732014)

## Check it

The Lean proof is a standard Lake project. Install
[elan](https://github.com/leanprover/elan#installation), then run:

```sh
cd lean
lake exe cache get
lake build
```

The build takes about an hour on two cores, with up to about 7.5 GB of
memory per Lean process. It checks the exact statement of the theorem and
of its four premises, the first thirty terms of the sequence, and that the
proof uses only Lean's standard axioms. [lean/README.md](lean/README.md)
explains the statement and the layout.

The four premises are checked by programs. With Python 3.10 or later, GNU
g++ and gcc, and `pip install -r checks/requirements.txt`, run from this
folder:

```sh
python3 checks/check.py quick --work /tmp/ekg-bounds-quick
```

This takes a few minutes. It checks the middle-range certificate in full
and rejects seven corrupted copies of it, and it replays the first
$10^8$ terms with both prefix programs and the direct minimality checker,
comparing them with the recorded results and rejecting two corrupted
prefixes. It does not recompute the full prefix. That is

```sh
python3 checks/check.py full --work /tmp/ekg-bounds-full
```

which runs both programs to $1.6 \times 10^{10}$ terms and compares every
recorded checkpoint; it takes about three hours and needs about 72 GB and
33 GB of memory for the two programs.
[checks/README.md](checks/README.md) gives the details.

## Credits

Jonathan Ayres discovered the sequence, as Lagarias, Rains and Sloane
credit in their [Introduction](https://arxiv.org/abs/math/0204011).
The conjecture, the published definition and the rule that each term is the least
unused multiple of a prime factor of its predecessor are due to
[Lagarias, Rains and Sloane (2002)](https://doi.org/10.1080/10586458.2002.10504486).
[Hofman and Pilipczuk (2008)](https://cs.uwaterloo.ca/journals/JIS/VOL11/Hofman/hofman1.html)
proved the full pattern $2p,p,3p$ for odd primes (by a
crossing count for $p > 25000$, and below that from Lagarias, Rains and
Sloane's computation) and the crossing lemma used throughout. Tomer Haver's
[*Explicit rates for the EKG sequence*](https://doi.org/10.5281/zenodo.23129632)
(version 3, October 2026, whose Lean archive is the one deposited with
version 2, unchanged) reduces that crossing count's computed base to
$p \le 43$ and formalizes the pattern and its consequences. Haver supplies the Lean
definition of the sequence, the counting identity and the explicit bounds
on early even terms, spans and missing composites, used here as proved Lean
theorems and sharpened in the middle range. The prime-counting bounds rest
on Rosser and Schoenfeld's (1962) bound for $\psi(x)$ and a form of
Chebyshev's (1852) lower bound, formalized
in [IEANTN](https://github.com/teorth/IEANTN) (T. Tao and contributors)
with [LeanCert (https://github.com/alerad/leancert)](https://github.com/alerad/leancert); the arithmetic large
sieve of Montgomery (1968) and Montgomery and Vaughan (1973) uses
OpenAI's [`OAI.Ostmann.publishedAdditiveLargeSieve`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/Ostmann/Preliminaries/AdditiveSieveProof.lean#L59),
the additive inequality for arbitrary complex weights, a shifted integer interval,
and reduced fractions with denominators at most $Q$. The retained statements
and proofs are preserved; imports are adapted to the local toolchain before
the arithmetic residue-avoidance inequality is deduced.
Lean, mathlib and their contributors supplied the formal infrastructure,
and the cover checker uses Arb through python-flint.

Haver's subsequent [Yellowstone work](https://doi.org/10.5281/zenodo.23604970) concerns a different greedy permutation; nothing from those papers is used here.

Related October 17–18 work by Haver treats the [lag-two EKG sequence (10.5281/zenodo.23437539)](https://doi.org/10.5281/zenodo.23437539), [general greedy-sieve processes (10.5281/zenodo.23437752)](https://doi.org/10.5281/zenodo.23437752), [a near-linear Yellowstone bound (10.5281/zenodo.23437783)](https://doi.org/10.5281/zenodo.23437783), [eight EKG-type rules (10.5281/zenodo.23437809)](https://doi.org/10.5281/zenodo.23437809), [closed Yellowstone-ladder results (10.5281/zenodo.23437816)](https://doi.org/10.5281/zenodo.23437816), and [Yellowstone II (10.5281/zenodo.23449375)](https://doi.org/10.5281/zenodo.23449375). These treat variants and general frameworks, including an EKG instance of the asymptotic theory in the general greedy-sieve paper; no additional theorem or code from these six papers is used here.

Other nearby rules are the [Yellowstone permutation of Applegate, Havermann, Selcoe, Shevelev, Sloane and Zumkeller](https://arxiv.org/abs/1501.01669v2), [Basistha and Ionaşcu's coprime permutation](https://arxiv.org/abs/2302.02838v5), and [Na's real-multiplier visiting process](https://doi.org/10.5281/zenodo.23138274). Nothing from these works is used here.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamEkgBounds2026,
  author       = {Graham, P.},
  title        = {{Sharp linear bounds for the EKG sequence}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/ekg-bounds-v4/results/ekg-bounds}},
  doi          = {10.5281/zenodo.23732014}
}
```
