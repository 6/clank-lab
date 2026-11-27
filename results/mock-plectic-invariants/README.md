# Numerical nonvanishing of mock plectic invariants

[![Checks](https://github.com/6/clank-lab/actions/workflows/mock-plectic-invariants.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/mock-plectic-invariants.yml)

The rank of an elliptic curve counts independent rational points of infinite order. In 2023, Fornea and Gehrmann asked whether a cohomology class attached to a curve over an imaginary quadratic field detects a particular rank pattern. We certify that their class is nonzero in 16 of 18 examples chosen for the cost of the calculation and for the arithmetic cases they test. Two examples remain inconclusive. A finite test published in the cosmosgeek0/BSD archive makes it possible to recognize nonvanishing from one coefficient. [Elliptic curves](https://mathworld.wolfram.com/EllipticCurve.html) · [Conjecture 2.13](https://arxiv.org/pdf/2311.03100v2) · [Finite-moment test](https://github.com/cosmosgeek0/BSD/blob/8f077506c503207a2ff675f8a5bcbba63398c911/finite-selmer-certificate.tex)

Computer-assisted; not yet reviewed by experts.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.24576819](https://doi.org/10.5281/zenodo.24576819)

## Abstract

We certify nonvanishing of the mock plectic invariant for sixteen of eighteen triples consisting of a rational elliptic curve, an imaginary quadratic field and an inert prime of multiplicative reduction. In this cost-selected cohort the curve has rational rank two and its quadratic twist has rank zero. Fornea and Gehrmann related the invariant to the first anticyclotomic derivative of a Heegner class. Their explicit reciprocity law turns a nonzero linear coefficient of a finite theta element into a witness. We compute the coefficients by evaluating a residual quaternionic eigenfunction on ring-class orbits. Two searches remain inconclusive. The public cosmosgeek0/BSD archive gave the finite-moment criterion and a witness at conductor 109, which we reproduce independently. A second table gives six nonvanishing certificates, five beyond the cohort. Assuming the divisor inequality of Fornea and Gehrmann's Theorem 3.3 at the augmentation prime, the six unit coefficients give an index bound. Under the same hypothesis, for their conductor-817 example the strict Selmer characteristic ideal has one exceptional factor fewer than the square of the Heegner index, and the extended Selmer group realizes the square. Under Fornea's comparison theorem the six coefficients also detect plectic Heegner classes.

This work has not yet been reviewed by experts. The proofs, computations, code and text were produced by AI models from OpenAI and Anthropic, working under the author's direction.

## Check it

Create the SageMath environment with `conda env create -f checks/environment.yml`. From this folder, replay both tables with one command. Allow about seven minutes of single-core computation and 2 GiB of memory after installation.

```sh
conda run -n mock-plectic python checks/replay.py
```

The two tables contain 23 distinct triples. One further stored record, for 389a1, was screened out before evaluating a theta coefficient. Its obstruction label records a rank-pattern test whose vanishing interpretation requires hypothesis (H) of the paper. The replay compares the complete stored records, including the coefficient vectors, the digests of the arithmetic checks, and the cap decisions for uncomputed primes. [Cohort records](data/cohort.jsonl) · [Additional records](data/additional.jsonl)

The weaker exponent bound in Section 3 uses the model of 817a1. In SageMath, the coefficient of degree two in `EllipticCurve([0,1,1,1,6]).padic_lseries(19).series(3)` reduces to 2 modulo 19. For the open height comparison, in PARI/GP set `E=ellinit([0,1,1,1,6])`. For each of `P=[-3/4,15/8]` and `P=[4,9]`, the command `valuation(ellpadiclog(E,19,8,ellmul(E,P,40)),19)` returns 1. The application of the height formula remains open.

### Cohort selection

From this folder, run `conda run -n mock-plectic python checks/census_select.py` to download the pinned Cremona data and compare the regenerated list with the archive. Expect 816 eligible triples, 676 supported ($N^-=1$), and 15 cost-selected. These have $p\le19$ and a least positive-sign admissible prime $\ell\le271$ with at most 4,000 raw flags. The CSV marks the three explicitly added cases separately. A blank prime means none qualified through 271. Add `--output candidates.csv` to write a fresh copy, or use `--dataset FILE` for a local copy of the input. [Candidate list](data/candidates.csv) · [Selection script](checks/census_select.py)

### Novelty

The literature and public archive searches located no earlier nonvanishing computation for a triple in this table. The archive already gives the conductor-109 witness and the general index bound, which we apply assuming FG Theorem 3.3 at the augmentation prime. Its November 26 snapshot contains no witness located for the remaining five unit applications or an exact exponent for 817a1 over the field of discriminant −7. [Archive manuscript, §6](https://github.com/cosmosgeek0/BSD/blob/a126723992b9be0c02b3b7a56dc245781b6c0d30/finite-selmer-certificate.tex)

## Credits

Darmon and Fornea introduced mock plectic points. Fornea and Gehrmann defined the invariant studied here, formulated the rank prediction, and proved the derivative and reciprocity laws used in every certificate. Fornea subsequently related the invariant to plectic Heegner classes. [Darmon–Fornea](https://arxiv.org/abs/2310.16758) · [Fornea–Gehrmann](https://arxiv.org/abs/2311.03100v2) · [Fornea](https://arxiv.org/abs/2603.28327v2)

On November 24, 2026, the cosmosgeek0/BSD archive reported the nonzero coefficient for 109a1 over the field of discriminant −8 in record 04 §§227–228. Our calculation at the same auxiliary prime independently reproduces that conclusion. The archive developed the finite-moment criterion and the general unit-index argument applied here. The certificate calculations use SageMath’s elliptic curves, quaternion algebras, lattices and quadratic forms. [Dated record](https://github.com/cosmosgeek0/BSD/blob/ed9c8ab32e5b30b4818ab2f0c3004022183f297d/bsd-research-history.zip) · [Dated finite-moment criterion](https://github.com/cosmosgeek0/BSD/blob/8f077506c503207a2ff675f8a5bcbba63398c911/finite-selmer-certificate.tex) · [Index argument, §6](https://github.com/cosmosgeek0/BSD/blob/a126723992b9be0c02b3b7a56dc245781b6c0d30/finite-selmer-certificate.tex#L228-L280)

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamMockPlecticInvariants2026,
  author = {Graham, Peter},
  title = {{Numerical nonvanishing of mock plectic invariants}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/mock-plectic-invariants-v3/results/mock-plectic-invariants}},
  doi          = {10.5281/zenodo.24576819}
}
```
