# Nonexistence of (243,121,60) difference sets in C3 × C9 × C9

[![Checks](https://github.com/6/clank-lab/actions/workflows/difference-set-243.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/difference-set-243.yml)

A difference set is a collection of points in a finite group whose ordered
differences represent every nonzero group element equally often.
[Gordon's La Jolla Difference Set Repository](https://dmgordon.org/difference-sets/)
[lists](https://doi.org/10.5281/zenodo.19740740) the question whether 121 points
in $C_3 \times C_9 \times C_9$ can represent each nonzero element exactly 60 times as open;
Gordon called it the “Smallest Open Case” in his
[August 3, 2019 presentation, slide 38](https://web.archive.org/web/20240502201448/https://cargo.wlu.ca/ArasuFest/ArasuFest_talks/Dan_Gordon.pdf#page=49).
It was already unresolved in Vera López and García Sánchez's 1997 table.
We prove that no such set exists. The conclusion concerns these parameters
in this group only.

Computer-assisted; not yet reviewed by experts.

The proofs, the Lean formalization, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23534853](https://doi.org/10.5281/zenodo.23534853)

## Check it

The executable checks require Python 3.10 or later and GNU g++ with C++20 and
OpenMP support, with no third-party Python packages. Use all allocated cores
as N and a new output directory outside this folder:

```sh
python3 checks/check.py quick --threads N --work /tmp/difference-set-243-quick
```

This bounded check validates finite structure, compiled options, positive
controls and corruptions. It is not an exhaustive lifting replay.
The complete executable check regenerates the finite cover and replays all
three complete kernels; allow hundreds of CPU-hours and distribute the
independent ranges as described in [checking details](checks/README.md):

```sh
python3 checks/check.py full --threads N --work /tmp/difference-set-243-full
```

The mathematical reduction is a standard Lean project. With elan installed,
run from this directory:

```sh
cd lean
lake exe cache get
lake build
```

Coverage of the 1,038-piece decomposition is proved independently of the two
production searches. Lean's `DS243.coverage` proves from the difference-set
definition that every possible set has a legal normalized image below an ID
in one of the pieces; it assumes no frontend or search outputs. A separately
written exhaustive cover checker also compares every actual prefix decoder
record and all option families with the group definitions, and rejects planted
missing-prefix, missing-option and missing-case gaps. Run it separately with
`python3 checks/check.py cover --threads N --work /tmp/difference-set-243-cover`.
Agreement between the fast and direct searches alone does not prove coverage.
Their common decomposition and options are stated explicitly in the paper.

The final Lean nonexistence theorem assumes the 1,038 semantic assertions
`RangeClear r` established by the external exhaustive computation. Lean does
not infer these assertions from digest strings or verify C++ execution.
The conditional boundary and the complete separately written third kernel
are explained in the paper and [checking details](checks/README.md).

## Credits

Daniel M. Gordon maintained the La Jolla repository, singled out this exact
case and connected it to the earlier literature. A. Vera López and M. A.
García Sánchez recorded it as unresolved in their 1997 systematic study and
used multiplier searches for related cases. Hall, Menon and Turyn developed
the multiplier and character methods underlying the reduction. Arasu and Ma,
Lander, Leung and Schmidt supplied earlier nonexistence results and
field-descent theory; Miller's explicit restatement helps distinguish their
hypotheses from this case. Paley's construction and Lehmer's historical work
supply the neighboring positive case. Recent related work is credited and
its scope distinguished in the paper. Lean, mathlib and their library
contributors supplied the formal-development infrastructure.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamDifferenceSet2432026,
  author       = {Graham, P.},
  title        = {{Nonexistence of (243,121,60) difference sets in C3 × C9 × C9}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/difference-set-243-v2/results/difference-set-243}},
  doi          = {10.5281/zenodo.23534853}
}
```
