# Third-party material

`data/krew_tables.json` transcribes 106 rows of the tables in Section 3.6 of Victor Reiner and Eric
Sommers, *Weyl group q-Kreweras numbers and cyclic sieving*, Annals of Combinatorics 22 (2018),
819–874 ([arXiv:1605.09172v2](https://arxiv.org/abs/1605.09172v2)): the Bala–Carter labels, the
exponents and the formulas for the q-Kreweras numbers, each also kept as the LaTeX printed there. They
are reproduced as mathematical data, with attribution, so that the checks can be run; the paper and the
README credit the work. No other text of the article is reproduced.

The Lean project downloads [Lean](https://github.com/leanprover/lean4) and
[Mathlib](https://github.com/leanprover-community/mathlib4), both under Apache-2.0, and Mathlib's
dependencies at the revisions in `lean/lake-manifest.json`; they keep their own licenses and are not
redistributed here. The checks install [python-flint](https://github.com/flintlib/python-flint) (its
package metadata declares MIT and LGPL-3.0-or-later, for the FLINT library it includes) and
[NumPy](https://numpy.org) (BSD-3-Clause) from PyPI; neither is redistributed here.

The proof sources, checkers, certificates and paper in this folder are covered by the repository's
Apache-2.0 license.
