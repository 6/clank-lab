# Nonexistence of (243,121,60) difference sets in C3 × C9 × C9

[![Checks](https://github.com/6/clank-lab/actions/workflows/difference-set-243.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/difference-set-243.yml)

A difference set is a collection of points in a finite group whose ordered
differences represent every nonzero group element equally often.
[Gordon's La Jolla Difference Set Repository](https://dmgordon.org/difference-sets/)
[listed](https://doi.org/10.5281/zenodo.19740740) the question whether 121 points
in $C_3 \times C_9 \times C_9$ can represent each nonzero element exactly 60 times as open in its April 24, 2026 archive;
Gordon called it the “Smallest Open Case” in the
[August 3, 2019 presentation, slide 38](https://web.archive.org/web/20240502201448/https://cargo.wlu.ca/ArasuFest/ArasuFest_talks/Dan_Gordon.pdf#page=49).
It was already unresolved in Vera López and García Sánchez's 1997 table.
[Keita Baba first proved that no such set exists on October 4, 2026](https://github.com/kei825/open-questions-2026/tree/d40fc3a3ac538e08e1bc31cf45b5d1204a2c34c8/space/difference-set-243),
by a SAT computation with a certificate accepted by the formally verified
checker cake_lpr and by lrat-check. We give an independent proof by a different
method: a lifting search with the reduction checked in Lean. The conclusion
concerns these parameters in this group only.

Computer-assisted; not yet reviewed by experts.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23647301](https://doi.org/10.5281/zenodo.23647301)

## Abstract

A $(243,121,60)$ difference set in $C_3\times C_9\times C_9$ would be a 121-element subset whose ordered differences represent every nonzero element exactly 60 times; we prove that none exists. Vera López and García Sánchez recorded this case as unresolved, and Gordon singled it out in a presentation on the La Jolla Difference Set Repository. Keita Baba proved this first, by a SAT computation with a certificate accepted by a formally verified checker; we give an independent proof by a different method. It builds on the fixed-translate theorem of McFarland and Rice, the multiplier and character methods of Hall, Menon and Turyn, and the multiplier searches of Vera López and García Sánchez. Using the multiplier 61, we reduce any such set, up to symmetry, to eight explicit patterns of coset sizes; an exhaustive search shows that none extends to a difference set. Lean proves the whole reduction; the formal nonexistence theorem assumes only the search results, which independent programs establish outside Lean.

This work has not yet been reviewed by experts. The proofs, the Lean formalization, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

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

Keita Baba's [No (243,121,60) difference set in Z3 × Z9 × Z9](https://github.com/kei825/open-questions-2026/tree/d40fc3a3ac538e08e1bc31cf45b5d1204a2c34c8/space/difference-set-243) is the first proof of this theorem; the present work is an independent confirmation by a different method. Daniel M. Gordon's [La Jolla Difference Sets Repository](https://doi.org/10.5281/zenodo.19740740) records the exact case and connects it to earlier literature. Gordon's [The La Jolla Difference Set Repository](https://web.archive.org/web/20240502201448/https://cargo.wlu.ca/ArasuFest/ArasuFest_talks/Dan_Gordon.pdf#page=49) singles it out as the smallest open case.

Marshall Hall Jr.'s [A Survey of Difference Sets](https://doi.org/10.1090/S0002-9939-1956-0082502-7) and P. K. Menon's [Difference sets in Abelian groups](https://doi.org/10.1090/S0002-9939-1960-0117169-3) provide multiplier-method background. R. L. McFarland and B. F. Rice's [Translates and multipliers of abelian difference sets](https://doi.org/10.1090/S0002-9939-1978-0462976-4) supplies the fixed translate used in the first step. R. J. Turyn's [Character sums and difference sets](https://doi.org/10.2140/pjm.1965.15.319) provides the character methods underlying the reduction. The Lean contributors' [Lean 4](https://github.com/leanprover/lean4) and the mathlib contributors' [mathlib](https://github.com/leanprover-community/mathlib4) supply the proof assistant and formal-development libraries.

The checking documentation also gives further credits and source notes.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamDifferenceSet2432026,
  author       = {Graham, Peter},
  title        = {{Nonexistence of (243,121,60) difference sets in C3 × C9 × C9}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/difference-set-243-v5/results/difference-set-243}},
  doi          = {10.5281/zenodo.23647301}
}
```
