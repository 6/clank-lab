# The seventh ternary density Hales–Jewett number

[![Checks](https://github.com/6/clank-lab/actions/workflows/density-seven.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/density-seven.yml)

A combinatorial line in a grid of words replaces the same chosen positions by each of three letters in turn. How many seven-letter words can one choose without taking a whole line? This is a different question from the density Hales–Jewett theorem itself (Furstenberg and Katznelson, 1991; an elementary proof by D.H.J. Polymath), which shows such sets take up a vanishing fraction of all words as the length grows. The exact largest size was known only up to six letters (Polymath, 2009). Polymath1's bounds were $1302 \le c_{7,3} \le 1348$ in 2009, as [Tao's March 4 post](https://terrytao.wordpress.com/2009/03/04/dhj3-900-999-density-hales-jewett-type-numbers/) records and [O'Bryant's 2015 paper](https://cs.uwaterloo.ca/journals/JIS/VOL18/OBryant/obr3.pdf) repeats. [D.H.J. Polymath's 2010 paper](https://arxiv.org/abs/1002.0374) tentatively conjectured 1302. We prove the matching unrestricted upper bound, closing that gap and determining the next value of [OEIS A156989](https://oeis.org/A156989). The supplied witness realizes Polymath's known lower bound.

Computer-assisted; not yet reviewed by experts.

The proofs, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23752609](https://doi.org/10.5281/zenodo.23752609)

## Check it

On Linux, install Python 3.10 or later, Git, a C/C++ compiler, Make and Rust/Cargo. From this folder:

```sh
python3 checks/build_tools.py /tmp/density-tools
python3 checks/check.py --quick --tools /tmp/density-tools --work /tmp/density-quick
```

This checks the complete reduction and witness, and a small refutation with corruption controls, in about ten minutes after building the tools. Replaying the full upper-bound computation requires:

```sh
python3 checks/check.py --full --tools /tmp/density-tools --work /tmp/density-full
```

Allow roughly 100 CPU-hours plus checking overhead, several days elapsed, and more than 59 GiB of memory for the largest cases. The quick CI check does not replay the main refutations. [Checking details and dependencies](checks/README.md).

## Credits

D.H.J. Polymath's [Density Hales–Jewett and Moser numbers](https://arxiv.org/abs/1002.0374v2) supplies the lower bound, conjecture and finite-density framework for this result. The witness realizes that known lower bound; the upper-bound computation establishes that no larger set exists in the seven-letter ternary grid. Y. Mouhib's [Lower Bounds for the Hales-Jewett Numbers via Symmetric and One-Weight Colorings](https://arxiv.org/html/2606.22155v2) provides adjacent coloring bounds.

The certificate computation uses Armin Biere and contributors' [CaDiCaL](https://github.com/arminbiere/cadical). Mario Carneiro's [FRAT-rs](https://github.com/digama0/frat) checks the proof certificates, and Marijn Heule's [drat-trim](https://github.com/marijnheule/drat-trim) supplies the standalone LRAT checker. Marijn Heule, Magnus Myreen and Yong Kiam Tan's [cake_lpr](https://github.com/tanyongkiam/cake_lpr) independently checks the proof certificates used to establish the upper bound.

The checking documentation also gives further credits and source notes.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamDensitySeven2026,
  author       = {Graham, P.},
  title        = {{The seventh ternary density Hales--Jewett number}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/density-seven-v5/results/density-seven}},
  doi          = {10.5281/zenodo.23752609}
}
```
