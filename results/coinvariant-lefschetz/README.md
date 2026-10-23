# The strong Lefschetz property for complex reflection coinvariants

[![Checks](https://github.com/6/clank-lab/actions/workflows/coinvariant-lefschetz.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/coinvariant-lefschetz.yml)

A [complex reflection group](https://en.wikipedia.org/wiki/Complex_reflection_group) acts on polynomials, and its coinvariant ring is the quotient obtained by setting all positive-degree invariant polynomials to zero. The strong Lefschetz property asks for one linear form whose powers give maps of the largest possible rank between every pair of homogeneous pieces. Wachi's question for these rings is documented in [2013](https://doi.org/10.34508/repsympo.2013.0_140). Earlier work established all irreducible types except the exceptional group $G_{34}$. This work proves that case by exact certificates, completing the irreducible classification. The paper then removes fixed coordinates and uses the tensor-product theorem to prove the assertion for every finite complex reflection group over $\mathbb{C}$.

The result builds on Harima and Watanabe's monomial-family theorem, the rank-two theorem of Harima, Migliore, Nagel and Watanabe, McDaniel's real-reflection theorem, and Wachi's computations for eight exceptional types, including $G_{33}$. The new proof uses Conway and Sloane's construction as developed by Oura and Sekiguchi, together with the free-extension results of Harima and Watanabe and of McDaniel, Chen, Iarrobino and Macias Marques.

Computer-assisted; not yet reviewed by experts.

The proofs, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23605134](https://doi.org/10.5281/zenodo.23605134)

## Check it

Use Python 3.11 or later, a C++17 compiler with OpenMP, FLINT and GMP development libraries, Singular 4, and GNU time. On Debian or Ubuntu, install the native requirements with `sudo apt-get install g++ libflint-dev libgmp-dev singular time python3-venv`. From this folder:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r checks/requirements.txt
python3 checks/verify.py --workers 2
```

The command reconstructs the large transformation witness locally from the included recipe, then checks it against the supplied input and basis certificates with both independent arithmetic implementations. It also checks the group action, input identities, finite monomial cover, multiplication ranks, and rejection of altered certificates. The paper proves the reduction to characteristic zero and applies the cited results for the other types; these arguments are not checked by Lean. Allow several gigabytes of temporary disk space. The paper source builds with XeLaTeX and the IPA Mincho font. See [the checker guide](checks/README.md) for the format, individual checks, and trusted software.

## Credits

Akihito Wachi formulated the complex-reflection question and established the eight exceptional cases used here. Tadahito Harima and Junzo Watanabe proved the monomial-family cases and developed free-extension methods; Harima, Juan Migliore, Uwe Nagel and Watanabe proved the two-variable result. Chris McDaniel proved the real-reflection result; the earlier history includes Borel's flag-variety identification, Richard Stanley's applications of hard Lefschetz to Weyl groups, and work of Toshiaki Maeno, Yasuhide Numata and Wachi on the noncrystallographic cases. Sachiko Yoshida studied Lefschetz elements for related rank-two groups. John Conway and Neil Sloane constructed the 756-vector model used by Manabu Oura and Jiro Sekiguchi. McDaniel, Shujian Chen, Anthony Iarrobino and Pedro Macias Marques supplied the tensor-product and free-extension results used here. Shephard and Todd classified the groups. The paper gives exact references and discusses nearby work by Larry Smith, Watanabe, and Kriebel. The checkers use SymPy, FLINT, GMP and Singular.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamCoinvariantLefschetz2026,
  author       = {Graham, P.},
  title        = {{The strong Lefschetz property for complex reflection coinvariants}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/coinvariant-lefschetz-v1/results/coinvariant-lefschetz}},
  doi          = {10.5281/zenodo.23605134}
}
```
