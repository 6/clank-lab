# The Turán density of the tight five-cycle

[![Checks](https://github.com/6/clank-lab/actions/workflows/tight-cycle-c5-turan.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/tight-cycle-c5-turan.yml)

A tight five-cycle has five cyclically consecutive triples on five vertices. Its avoidance density is $2\sqrt3-3$, settling [Mubayi–Pikhurko–Sudakov's 2011 conjecture](https://opikhurko.warwick.ac.uk/E/MubayiPikhurkoSudakov11aim.pdf) via [Bodnár–León–Liu–Pikhurko reduction](https://arxiv.org/abs/2506.03223v1).

Checked in Lean from the definitions, with compiled evaluation; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23743820](https://doi.org/10.5281/zenodo.23743820)

## Check it

Python 3.12+, C++17/OpenMP, GMP; [instructions](checks/README.md).

```sh
python3 -m pip install -r checks/requirements.txt
python3 -I checks/quickcheck.py --cpus 2
```

## Credits

Dhruv Mubayi and Vojtěch Rödl conjectured the value in [*On the Turán number of triple systems*](https://doi.org/10.1006/jcta.2002.3284) (2002) and gave the recursive construction this result proves extremal; Mubayi, Pikhurko and Sudakov restated it as Conjecture 7 of [*Hypergraph Turán problem: some open questions*](https://opikhurko.warwick.ac.uk/E/MubayiPikhurkoSudakov11aim.pdf). The proof uses Alexander Razborov's [flag algebras](https://doi.org/10.2178/jsl/1203350785), whose earlier [bound of 0.4683](https://doi.org/10.1137/090747476) it improves to the exact value. It builds most directly on Levente Bodnár, Jared León, Xizhi Liu and Oleg Pikhurko's [*The Turán density of short tight cycles*](https://arxiv.org/abs/2506.03223), whose partition reduction and [certificate notebook](https://github.com/bodnalev/supplementary_files/blob/5766324d010da24a66271c0fbe38460cd377985b/no_cl/no_c5_k4.ipynb) it follows, computed with Bodnár's [FlagAlgebraToolbox](https://arxiv.org/abs/2601.06590). Kamčev, Letzter and Pokrovskiy [settled long tight cycles](https://arxiv.org/abs/2209.08134); Falgas-Ravry and Vaughan's [Turán H-densities](https://arxiv.org/abs/1201.4326) and Huang's [directed stars](https://arxiv.org/abs/1303.3101) give the bound behind the construction's blowups; and Jeong, Park, Hyun, Oum and Yang [formalize flag algebras in Lean](https://arxiv.org/abs/2607.23500). Lean and [mathlib](https://github.com/leanprover-community/mathlib4) supply formal mathematics.

Many other works informed approaches tried along the way or are close to this one; [the checking guide](checks/README.md#further-credits) credits each of them with a link.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamTightCycleC5Turan2026,
  author       = {Graham, P.},
  title        = {{The Turán density of the tight five-cycle}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/tight-cycle-c5-turan-v1/results/tight-cycle-c5-turan}},
  doi          = {10.5281/zenodo.23743820}
}
```
