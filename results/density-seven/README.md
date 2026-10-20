# The seventh ternary density Hales–Jewett number

[![Checks](https://github.com/6/clank-lab/actions/workflows/density-seven.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/density-seven.yml)

A combinatorial line in a grid of words replaces the same chosen positions by each of three letters in turn. How many seven-letter words can one choose without taking a whole line? [D.H.J. Polymath](https://arxiv.org/abs/1002.0374) gave a construction in 2010 and conjectured it was best possible. We prove the matching unrestricted upper bound, so the maximum is 1302, determining the next value of [OEIS A156989](https://oeis.org/A156989). The construction and the conjectured value are Polymath's.

Computer-assisted; not yet reviewed by experts.

The proofs, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23491269](https://doi.org/10.5281/zenodo.23491269)

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

Allow at least about 75 CPU-hours, plus drat-trim checking and audits, and several days elapsed. About 1.56 TB of generated proof text passes through pipes rather than being saved. The quick CI check does not replay the main refutations. [Checking details and dependencies](checks/README.md).

## Credits

D.H.J. Polymath gave the construction, the conjecture and the finite-density framework. The proof checking uses CaDiCaL (Armin Biere and its contributors), FRAT-rs (Mario Carneiro), drat-trim (Marijn Heule) and cake_lpr (Marijn Heule, Magnus Myreen and Yong Kiam Tan).

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamDensitySeven2026,
  author       = {Graham, P.},
  title        = {{The seventh ternary density Hales--Jewett number}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/density-seven-v1/results/density-seven}},
  doi          = {10.5281/zenodo.23491269}
}
```
