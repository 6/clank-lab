# The certificate checks

These programs check the finite identities that, by Section 2 of the paper, imply the theorem. They
need Python 3.12 or later with the packages in `requirements.txt` (python-flint and NumPy, pinned by
version and file hash). From the folder above this one:

```sh
python3 -m pip install -r checks/requirements.txt
sh checks/check.sh
```

`check.sh` runs twelve checks and ends with `PASS: 12 of 12 checks (part 1 of 1)`; any failure stops it
with a nonzero exit. `sh checks/check.sh --part K/N` runs the checks numbered K, K + N, K + 2N, …, so N
machines can share them. On one core the whole run takes about four minutes, most of it E8, with a peak
of about 900 MB of memory.

## The programs

- `coxeter.py` builds the simple reflections of G2, F4, E6, E7 and E8 from the symmetrized Cartan
  matrices (Bourbaki numbering) and checks that `c = s_1 ⋯ s_n` has order exactly `h` and that
  `rank(c - 1) = n`. These are the facts about `c` that the Lean statement takes as hypotheses.
- `check_a.py TABLES CERT` (checker A) builds the root system, the reflections as integer matrices and
  `NC(W)` bottom-up with exact ranks, checks `|NC(W)|` against the Catalan number of `W` and the number of
  comparable pairs against the Fuss–Catalan number `Cat^(2)(W)`, and labels each class of flats by the
  Dynkin type of a conjugate standard parabolic subset (found by elementary moves
  `J ↦ w₀(J ∪ {s}) J w₀(J ∪ {s})`) and the number of restricted hyperplanes. It recomputes the fixed-point
  polynomials of Step 2 for every `(h₁, ν)`, evaluates each table formula as an exact polynomial in
  `ℤ[q]` (the division is checked exact) reduced modulo the cyclotomic polynomial `Φ_d`, and compares
  both sides for `m₁ = 1, …, n + 2`. It also checks the row shapes and the facts used for `ν > n`.
- `check_b.py TABLES CERT S` (checker B) shares no code with checker A. `W` acts by permutations of the
  roots; `V^w` is spanned by the root-orbit sums of `w`; `NC(W)` is built top-down from `c` by lower
  covers; classes of flats are identified by an invariant of `V^w`; the block exponents come from
  iterating the twisted rotation symbolically; and each right side is evaluated from the leading terms
  of its factors at `q = ω e^ε` in `ℚ(ζ_d)`. It recounts fixed points by brute force, applying the
  Bessis–Reiner generator (6.4) literally for `s ≤ S` and the twisted rotation for slightly larger `s`
  (`check.sh` uses `S = 4, 3, 2, 1, 1` for G2, F4, E6, E7, E8).
- `corrupt.py TABLES CERT_E6` makes six corrupted copies of the E6 data (a coefficient changed, a case
  removed, two labels swapped, an exponent changed, a bracket changed, an exponent made nonlinear in `m`)
  and requires each checker to reject each one with the expected reason.
- `tables/` holds the transcription of the tables: `extract.py` reads the rows of Reiner and Sommers'
  Section 3.6 from the LaTeX source of arXiv:1605.09172v2, and `convert.py` turns them into the
  formulas of `../data/krew_tables.json`. `sh checks/tables/regen.sh` downloads the source, checks its
  SHA-256 and regenerates the file byte for byte; it needs network access and is not run by `check.sh`.

The certificates in `../data/` were produced by a separate search program, which is not included: both
checkers recompute every entry from the root system and the tables, so nothing in the certificate is
taken on trust. The checkers' comments call it "the search program". [The data notes](../data/README.md)
describe the formats and list the labels of the classes of flats.

Each checker prints one line per type, for example for E8

```text
{"type": "E8", "status": "ACCEPT", "nc": 25080, "pairs": 1520922, "classes": 41, "pairs_h1_m2": 38, "large_m2": 10, "max_denominator": 30}
{"type": "E8", "status": "ACCEPT", "nc": 25080, "classes": 41, "pairs_h1_m2": 38, "large_m2": 10, "brute_s_literal": 1, "brute_s_rotation": 2}
```

## How the checks relate to the theorem

For each type the checks establish the hypotheses of the Lean theorem `RS16.Main.conjecture_1_4`
([Lean details](../lean/README.md) match each hypothesis to the lines of `check_a.py` that check it).
The identities with `d = 1` are the refined Kreweras counts at `q = 1`, which Douvropoulos and
Josuat-Vergès proved; they hold for all `s`, which also fixes the convention that the class is read from
the bottom element of the multichain. The 106 table rows used were compared one by one with the
rendered journal pages 22–30 of Reiner and Sommers' paper (exponents, numerators, sums and
denominators); they agree.

## Further credits

- V. Reiner and E. Sommers, Weyl group q-Kreweras numbers and cyclic sieving, Ann. Comb. 22 (2018),
  819–874, [arXiv:1605.09172v2](https://arxiv.org/abs/1605.09172v2): Conjecture 1.4, Theorem 1.7 (types
  A, B, C, D) and the tables of Section 3.6, which `data/krew_tables.json` transcribes.
- T. Douvropoulos and M. Josuat-Vergès, The generalized cluster complex: refined enumeration of faces
  and related parking spaces, SIGMA 19 (2023), 069, [arXiv:2209.12540v2](https://arxiv.org/abs/2209.12540v2):
  Theorem 3.10, the case `q = 1`, which they attribute to Rhoades except for E7 and E8.
- C. A. Athanasiadis and V. Reiner, Noncrossing partitions for the group `D_n`, SIAM J. Discrete Math. 18
  (2004), 397–417, [doi:10.1137/S0895480103432192](https://doi.org/10.1137/S0895480103432192): Theorem 6.3,
  the case `s = 1` of the count at `q = 1`.
- B. Rhoades, Parking structures: Fuss analogs, J. Algebraic Combin. 40 (2014), 417–473,
  [arXiv:1205.4293](https://arxiv.org/abs/1205.4293).
- C. Krattenthaler and T. W. Müller, on cyclic sieving for complex reflection groups of exceptional
  type, in: I. S. Kotsireas and E. V. Zima (eds.), Advances in Combinatorics, Springer, 2013, 209–247
  (title in the paper's references), [doi:10.1007/978-3-642-30979-3_12](https://doi.org/10.1007/978-3-642-30979-3_12),
  [arXiv:1001.0028](https://arxiv.org/abs/1001.0028): the formula (5.1) for powers of the action, the
  parametrization and the block equations (5.8) from the proof of Lemma 30, and Lemma 31, on which Step 2
  is modeled.
- D. Bessis and V. Reiner, Cyclic sieving of noncrossing partitions for complex reflection groups, Ann.
  Comb. 15 (2011), 197–222, [arXiv:math/0701792](https://arxiv.org/abs/math/0701792): the form (6.4) of
  the action used here, and the question of q-Kreweras numbers for `s = 1` (Section 6.1, Question 6.3).
- D. Bessis, The dual braid monoid, Ann. Sci. École Norm. Sup. (4) 36 (2003), 647–683,
  [arXiv:math/0101158](https://arxiv.org/abs/math/0101158): the noncrossing partitions `NC(W)`.
- D. Armstrong, Generalized noncrossing partitions and combinatorics of Coxeter groups, Mem. Amer. Math.
  Soc. 202 (2009), no. 949: the multichains and the cyclic action, and Conjecture 5.4.7.
- R. W. Carter, Conjugacy classes in the Weyl group, Compositio Math. 25 (1972), 1–59: Lemma 2, reflection
  length as `rank(w - 1)`.
- Nearby work this result does not address: C. Krattenthaler and C. Stump, Positive m-divisible
  non-crossing partitions and their Kreweras maps, [arXiv:2506.14996v1](https://arxiv.org/abs/2506.14996v1),
  Section 7.2, Question 7.5 and Open Problem 7.6 (positive noncrossing partitions with prescribed block
  structure in exceptional types); L. Pouillart, Cyclic sieving phenomena on parabolic classes of faces
  of the cluster complex, [arXiv:2603.28242v1](https://arxiv.org/abs/2603.28242v1); D. Kim, q-Kreweras
  numbers for coincidental Coxeter groups attached to limit symbols,
  [arXiv:2012.08076](https://arxiv.org/abs/2012.08076).
- Software: [Lean 4](https://github.com/leanprover/lean4) and
  [Mathlib](https://github.com/leanprover-community/mathlib4); [python-flint](https://github.com/flintlib/python-flint)
  and [FLINT](https://flintlib.org); [NumPy](https://numpy.org).
