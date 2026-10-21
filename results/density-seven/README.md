# The seventh ternary density Hales–Jewett number

[![Checks](https://github.com/6/clank-lab/actions/workflows/density-seven.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/density-seven.yml)

A combinatorial line in a grid of words replaces the same chosen positions by each of three letters in turn. How many seven-letter words can one choose without taking a whole line? Polymath1's bounds were $1302 \le c_{7,3} \le 1348$ in 2009, as [Tao's March 4 post](https://terrytao.wordpress.com/2009/03/04/dhj3-900-999-density-hales-jewett-type-numbers/) records and [O'Bryant's 2015 paper](https://cs.uwaterloo.ca/journals/JIS/VOL18/OBryant/obr3.pdf) repeats. [D.H.J. Polymath's 2010 paper](https://arxiv.org/abs/1002.0374) tentatively conjectured 1302. We prove the matching unrestricted upper bound, closing that gap and determining the next value of [OEIS A156989](https://oeis.org/A156989). The supplied witness realizes Polymath's known lower bound.

Computer-assisted; not yet reviewed by experts.

The proofs, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23532529](https://doi.org/10.5281/zenodo.23532529)

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

Allow roughly 100 CPU-hours for solver and proof-checker work, plus drat-trim checking, audits and stream handling, and several days elapsed. The completed cake_lpr checks used heaps up to about 59 GiB. About 1.56 TB of generated proof text passes through pipes rather than being saved. The paper separates the measured historical computation from the eight additional cake_lpr checks. The quick CI check does not replay the main refutations. [Checking details and dependencies](checks/README.md).

## Credits

D.H.J. Polymath gave the known lower bound, the conjecture and the finite-density framework. The proof checking uses CaDiCaL (Armin Biere and its contributors), FRAT-rs (Mario Carneiro), drat-trim (Marijn Heule) and cake_lpr (Marijn Heule, Magnus Myreen and Yong Kiam Tan).

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamDensitySeven2026,
  author       = {Graham, P.},
  title        = {{The seventh ternary density Hales--Jewett number}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/density-seven-v3/results/density-seven}},
  doi          = {10.5281/zenodo.23532529}
}
```
