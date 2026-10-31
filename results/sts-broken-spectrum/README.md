# A Steiner triple system with a broken chromatic spectrum

[![Checks](https://github.com/6/clank-lab/actions/workflows/sts-broken-spectrum.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/sts-broken-spectrum.yml)

A [Steiner triple system](https://mathworld.wolfram.com/SteinerTripleSystem.html) is a set of points with a family of three-point blocks such that every two points lie in exactly one block; the [Fano plane](https://en.wikipedia.org/wiki/Fano_plane) is the smallest interesting one. A bicoloring colors the points so that every block gets exactly two colors, and the feasible set of the system is the set of numbers $k$ for which some bicoloring uses exactly $k$ colors. Mario Gionfriddo conjectured in 2003 that this set never has a gap, a conjecture he [restated in 2025](https://doi.org/10.3390/math14010042) and that Tuza and Voloshin listed as open in [their 2008 survey](https://doi.org/10.1007/978-3-540-77200-2_12). In [2014](https://ajc.maths.uq.edu.au/pdf/59/ajc_v59_p107.pdf) Gionfriddo, Guardo, Milazzo and Voloshin left open whether a system with 39 points can have feasible set $`\{3,5\}`$. We give a Steiner triple system with 39 points and 247 blocks that has bicolorings with exactly three and exactly five colors but none with exactly four, so the conjecture is false. The class sizes of its two bicolorings come from the tables of [Colbourn, Dinitz and Rosa](https://doi.org/10.37236/1457).

Together with the 2014 theorem that bicolorings of 39-point systems use three, four or five colors, the feasible set of this system is exactly $`\{3,5\}`$.

Computer-assisted; not yet reviewed by experts.

The proofs, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Python 3.9 or later and a C compiler are enough; [checks/requirements.txt](checks/requirements.txt) lists the requirements. From this folder, run:

```sh
python3 -I checks/verify.py
```

The command checks the system and both bicolorings from the definitions, rebuilds the four-color formula from the blocks and compares it with the one in `data/`, builds DRAT-trim and checks the proof that the formula is unsatisfiable, checks the same proof with a separate unit-propagation checker, and runs calibration and corruption tests. It takes a few seconds. The [checker documentation](checks/README.md) describes the files and what each check establishes.

## Credits

The question is Mario Gionfriddo's, posed in a 2003 lecture published in the Rendiconti del Seminario Matematico di Messina and restated in [his 2025 survey](https://doi.org/10.3390/math14010042); bicolorings are the strict colorings of Vitaly Voloshin's mixed hypergraphs. The work this result builds on most is Charles Colbourn, Jeffrey Dinitz and Alexander Rosa's [Bicoloring Steiner triple systems](https://doi.org/10.37236/1457), whose tables of realizable class sizes gave the sizes 10, 12, 17 and 1, 2, 4, 16, 16 used in the search, and Mario Gionfriddo, Elena Guardo, Lorenzo Milazzo and Vitaly Voloshin's [Feasible sets of small bicolorable STSs](https://ajc.maths.uq.edu.au/pdf/59/ajc_v59_p107.pdf), which posed the order-39 case and supplies the bound used for the exact feasible set.

The system was found with the SAT solver [CaDiCaL](https://github.com/arminbiere/cadical) by Armin Biere and collaborators, which also produced the proof of unsatisfiability, and that proof is checked with [DRAT-trim](https://github.com/marijnheule/drat-trim) by Nathan Wetzler, Marijn Heule and Warren Hunt. Tuza and Voloshin's survey and the work of Jiang, Mubayi, Tuza, Voloshin and West on broken spectra of mixed hypergraphs are credited, with other related work, in [Further credits](checks/README.md#further-credits).

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamStsBrokenSpectrum2026,
  author       = {Graham, P.},
  title        = {{A Steiner triple system with a broken chromatic spectrum}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/sts-broken-spectrum-v1/results/sts-broken-spectrum}}
}
```
