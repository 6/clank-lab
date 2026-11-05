# Data

- `krew_tables.json`: the 106 rows of Reiner and Sommers' Section 3.6 tables (arXiv:1605.09172v2) that
  belong to principal-in-a-Levi orbits with trivial φ: 4, 12, 17, 32 and 41 rows for G2, F4, E6, E7 and
  E8. Each row has the type, the Bala–Carter label (`label`, and `label_tex` as printed), the exponents
  of the second column (`exponents`, as printed in the row; `os_exponents`, the Orlik–Solomon exponents of
  the orbit, which for ten orbits add one exponent printed in a row with nontrivial φ), the formula as printed (`f_tex`) and the formula
  the checkers read (`f`), in which `B(x)` is the q-integer `[x]_q`, `q**(…)` a power of `q` and `m` the
  parameter. [The transcription scripts](../checks/tables/) regenerate it from the arXiv source.
- `G2.json`, …, `E8.json`: one certificate per type, with
  - `type`, `n`, `h`, `nc_size` (`|NC(W)|`), `pairs` (comparable pairs in the absolute order) and
    `max_denominator` (`b_max`);
  - `classes`: for each class of flats, a standard parabolic subset `J` (Bourbaki numbering, from 0)
    conjugate to the fixator, its `label` and `count_s1`, the number of `w` in `NC(W)` with `V^w` in the
    class;
  - `reduction`: for each `(h1, nu)` with `h1 | h`, `1 ≤ nu ≤ n` and `gcd(h1, nu) = 1`, the order
    `d = nu h/h1` and, for each label, the coefficients `a_0, …, a_n` of the fixed-point polynomial
    `L_X(m1) = Σ_k a_k binom(m1, k)`;
  - `large_m2`: the pairs `(h1, nu)` with `nu > n` and `d ≤ b_max`, checked separately;
  - `brute_small_s`: entries `[s, p, d, label, count]`, the number of delta sequences fixed by `φ^p`
    with that label, for small `s`, which checker B recounts by brute force.

## Classes of flats and their labels

`J` is the standard parabolic subset (Bourbaki numbering, from 0) conjugate to the fixator of `V^w`; the
label is the Bala–Carter label of the orbit principal in that Levi subalgebra; `#NC` is the number of `w`
in `NC(W)` with `V^w` in the class (the count for `s = 1`, `d = 1`). Both checkers recompute the labels
(checker A from the type of `J` and the number of restricted hyperplanes, checker B from an invariant of
`V^w`), and both distinguish root lengths (`A1` versus `~A1`, `B3` versus `C3`).
### G2

| J | label | #NC |
|---|---|---|
| [] | `0` | 1 |
| [0] | `~A1` | 3 |
| [1] | `A1` | 3 |
| [0, 1] | `G2` | 1 |

### F4

| J | label | #NC |
|---|---|---|
| [] | `0` | 1 |
| [1] | `A1` | 12 |
| [3] | `~A1` | 12 |
| [0, 1] | `A2` | 8 |
| [1, 2] | `B2` | 15 |
| [1, 3] | `A1+~A1` | 24 |
| [2, 3] | `~A2` | 8 |
| [0, 1, 2] | `B3` | 6 |
| [0, 1, 3] | `A2+~A1` | 6 |
| [0, 2, 3] | `~A2+A1` | 6 |
| [1, 2, 3] | `C3` | 6 |
| [0, 1, 2, 3] | `F4` | 1 |

### E6

| J | label | #NC |
|---|---|---|
| [] | `0` | 1 |
| [5] | `A1` | 36 |
| [3, 5] | `2A1` | 108 |
| [4, 5] | `A2` | 96 |
| [0, 3, 5] | `3A1` | 72 |
| [1, 4, 5] | `A2+A1` | 144 |
| [3, 4, 5] | `A3` | 135 |
| [0, 2, 4, 5] | `2A2` | 8 |
| [0, 3, 4, 5] | `A3+A1` | 60 |
| [1, 2, 3, 4] | `D4` | 22 |
| [1, 2, 4, 5] | `A2+2A1` | 54 |
| [2, 3, 4, 5] | `A4` | 60 |
| [0, 1, 2, 4, 5] | `2A2+A1` | 6 |
| [0, 1, 3, 4, 5] | `A4+A1` | 12 |
| [0, 2, 3, 4, 5] | `A5` | 6 |
| [1, 2, 3, 4, 5] | `D5` | 12 |
| [0, 1, 2, 3, 4, 5] | `E6` | 1 |

### E7

| J | label | #NC |
|---|---|---|
| [] | `0` | 1 |
| [6] | `A1` | 63 |
| [4, 6] | `2A1` | 315 |
| [5, 6] | `A2` | 231 |
| [1, 4, 6] | `(3A1)''` | 21 |
| [2, 4, 6] | `(3A1)'` | 315 |
| [3, 5, 6] | `A2+A1` | 693 |
| [4, 5, 6] | `A3` | 441 |
| [0, 3, 5, 6] | `A2+2A1` | 378 |
| [1, 2, 3, 4] | `D4` | 84 |
| [1, 2, 4, 6] | `4A1` | 63 |
| [1, 4, 5, 6] | `(A3+A1)''` | 63 |
| [2, 3, 5, 6] | `2A2` | 126 |
| [2, 4, 5, 6] | `(A3+A1)'` | 441 |
| [3, 4, 5, 6] | `A4` | 315 |
| [0, 1, 2, 4, 6] | `A2+3A1` | 21 |
| [0, 1, 3, 5, 6] | `2A2+A1` | 63 |
| [0, 2, 4, 5, 6] | `A3+A2` | 63 |
| [0, 3, 4, 5, 6] | `A4+A1` | 135 |
| [1, 2, 3, 4, 5] | `D5` | 72 |
| [1, 2, 3, 4, 6] | `D4+A1` | 36 |
| [1, 2, 4, 5, 6] | `A3+2A1` | 63 |
| [1, 3, 4, 5, 6] | `A5''` | 21 |
| [2, 3, 4, 5, 6] | `A5'` | 72 |
| [0, 1, 2, 3, 4, 5] | `E6` | 9 |
| [0, 1, 2, 3, 4, 6] | `D5+A1` | 9 |
| [0, 1, 2, 3, 5, 6] | `A4+A2` | 9 |
| [0, 1, 2, 4, 5, 6] | `A3+A2+A1` | 9 |
| [0, 1, 3, 4, 5, 6] | `A5+A1` | 9 |
| [0, 2, 3, 4, 5, 6] | `A6` | 9 |
| [1, 2, 3, 4, 5, 6] | `D6` | 9 |
| [0, 1, 2, 3, 4, 5, 6] | `E7` | 1 |

### E8

| J | label | #NC |
|---|---|---|
| [] | `0` | 1 |
| [7] | `A1` | 120 |
| [5, 7] | `2A1` | 945 |
| [6, 7] | `A2` | 595 |
| [3, 5, 7] | `3A1` | 1575 |
| [4, 6, 7] | `A2+A1` | 3060 |
| [5, 6, 7] | `A3` | 1485 |
| [0, 3, 5, 7] | `4A1` | 675 |
| [1, 2, 3, 4] | `D4` | 325 |
| [1, 4, 6, 7] | `A2+2A1` | 2700 |
| [3, 4, 6, 7] | `2A2` | 1000 |
| [3, 5, 6, 7] | `A3+A1` | 3300 |
| [4, 5, 6, 7] | `A4` | 1518 |
| [0, 3, 4, 6, 7] | `2A2+A1` | 600 |
| [0, 3, 5, 6, 7] | `A3+2A1` | 990 |
| [1, 2, 3, 4, 5] | `D5` | 390 |
| [1, 2, 3, 4, 7] | `D4+A1` | 390 |
| [1, 2, 4, 6, 7] | `A2+3A1` | 600 |
| [1, 4, 5, 6, 7] | `A4+A1` | 1380 |
| [2, 3, 5, 6, 7] | `A3+A2` | 990 |
| [3, 4, 5, 6, 7] | `A5` | 780 |
| [0, 1, 2, 3, 4, 5] | `E6` | 65 |
| [0, 1, 2, 4, 6, 7] | `2A2+2A1` | 90 |
| [0, 1, 3, 5, 6, 7] | `A3+A2+A1` | 180 |
| [0, 2, 4, 5, 6, 7] | `A4+A2` | 180 |
| [0, 3, 4, 5, 6, 7] | `A5+A1` | 195 |
| [1, 2, 3, 4, 5, 6] | `D6` | 105 |
| [1, 2, 3, 4, 5, 7] | `D5+A1` | 195 |
| [1, 2, 3, 4, 6, 7] | `D4+A2` | 65 |
| [1, 2, 3, 5, 6, 7] | `2A3` | 90 |
| [1, 2, 4, 5, 6, 7] | `A4+2A1` | 180 |
| [2, 3, 4, 5, 6, 7] | `A6` | 195 |
| [0, 1, 2, 3, 4, 5, 6] | `E7` | 15 |
| [0, 1, 2, 3, 4, 5, 7] | `E6+A1` | 15 |
| [0, 1, 2, 3, 4, 6, 7] | `D5+A2` | 15 |
| [0, 1, 2, 3, 5, 6, 7] | `A4+A3` | 15 |
| [0, 1, 2, 4, 5, 6, 7] | `A4+A2+A1` | 15 |
| [0, 1, 3, 4, 5, 6, 7] | `A6+A1` | 15 |
| [0, 2, 3, 4, 5, 6, 7] | `A7` | 15 |
| [1, 2, 3, 4, 5, 6, 7] | `D7` | 15 |
| [0, 1, 2, 3, 4, 5, 6, 7] | `E8` | 1 |
